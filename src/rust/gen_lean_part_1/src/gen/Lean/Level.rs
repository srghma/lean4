// Lean compiler output
// Module: Lean.Level
// Imports: Init.Data.Array.QSort Lean.Data.PersistentHashSet Lean.Hygiene Init.Data.Option.Coe Init.Data.Nat.Linear
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_borrowed,
    lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uset, lean_level_eq, lean_level_mk_data, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_shiftr, lean_nat_sub,
    lean_nat_to_int, lean_panic_fn_borrowed, lean_ptr_addr, lean_string_append, lean_string_length,
    lean_uint32_dec_eq, lean_uint32_to_nat, lean_uint32_to_uint64, lean_uint64_dec_eq,
    lean_uint64_land, lean_uint64_mix_hash, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_nat, lean_uint64_to_uint32, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::QSort::{
    initialize_Init_Data_Array_QSort, runtime_initialize_Init_Data_Array_QSort,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Option::Coe::{
    initialize_Init_Data_Option_Coe, runtime_initialize_Init_Data_Option_Coe,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toString;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_replacePrefix, l_Lean_Name_reprPrec, l_Lean_Name_reprPrec___boxed,
    l_Lean_Syntax_mkNumLit, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_num___override, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_UInt64_decEq___boxed, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_lt,
};
use crate::r#gen::Lean::Data::PersistentHashSet::{
    initialize_Lean_Data_PersistentHashSet, runtime_initialize_Lean_Data_PersistentHashSet,
};
use crate::r#gen::Lean::Hygiene::{initialize_Lean_Hygiene, runtime_initialize_Lean_Hygiene};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_forInStep___redArg;
static mut l_Lean_instInhabitedData___aux__1___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedData___aux__1___closed__0: u64 = 0;
pub static mut l_Lean_instInhabitedData___aux__1: u64 = 0;
pub static mut l_Lean_instInhabitedData: u64 = 0;
pub static l_Lean_instBEqData___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_decEq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqData___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqData: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqData___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__1_value: leanh::LeanStringObject<15> =
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
            32, 40, 104, 97, 115, 80, 97, 114, 97, 109, 32, 58, 61, 32, 0,
        ],
    };
static mut l_Lean_instReprData___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__3_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__4_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [32, 40, 104, 97, 115, 77, 86, 97, 114, 32, 58, 61, 32, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__5_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [76, 101, 118, 101, 108, 46, 109, 107, 68, 97, 116, 97, 32, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__6_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [32, 40, 100, 101, 112, 116, 104, 32, 58, 61, 32, 0],
    };
static mut l_Lean_instReprData___lam__0___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprData___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprData___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instReprData: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLevelMVarId_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLevelMVarId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqLevelMVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqLevelMVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqLevelMVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqLevelMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instHashableLevelMVarId_hash___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableLevelMVarId_hash___closed__0: u64 = 0;
static mut l_Lean_instHashableLevelMVarId_hash___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableLevelMVarId_hash___closed__1: u64 = 0;
pub static l_Lean_instHashableLevelMVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableLevelMVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableLevelMVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instHashableLevelMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value:
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value:
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value:
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLevelMVarId_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLevelMVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLevelMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLMVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_reprPrec___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLMVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLMVarId___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLMVarId___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedLMVarIdSet___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLMVarIdSet: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instEmptyCollectionLMVarIdSet___aux__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instEmptyCollectionLMVarIdSet: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Level_zero___override: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Level_data___override___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_data___override___closed__0: u64 = 0;
pub static mut l_Lean_instInhabitedLevel_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLevel: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprLevel_repr___closed__0_value: leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 122, 101, 114, 111, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprLevel_repr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevel_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLevel_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevel_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevel_repr___closed__4_value: leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 115, 117, 99, 99, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__5_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__7_value: leanh::LeanStringObject<15> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__8_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__8_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__10_value: leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 105, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__11_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__10_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__12_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__11_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__13_value: leanh::LeanStringObject<17> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 112, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__14_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__13_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__15_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__14_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__16_value: leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__17_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__16_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__18_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__17_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprLevel___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLevel_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLevel___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instReprLevel: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_instHashable___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instHashable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Level_instHashable: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instHashable___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_levelZero: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Level_one___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_one___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Level_one: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_levelOne: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Level_mvarId_x21___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 0],
    };
static mut l_Lean_Level_mvarId_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_mvarId_x21___closed__1_value: leanh::LeanStringObject<19> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 109, 118, 97, 114, 73, 100, 33, 0,
        ],
    };
static mut l_Lean_Level_mvarId_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_mvarId_x21___closed__2_value: leanh::LeanStringObject<22> =
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
            109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 101, 120, 112, 101, 99,
            116, 101, 100, 0,
        ],
    };
static mut l_Lean_Level_mvarId_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Level_mvarId_x21___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_mvarId_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_instBEq___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_Level_instBEq: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Level_normalize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__2_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Level_normalize___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__1_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 110, 111, 114, 109, 97, 108, 105,
            122, 101, 0,
        ],
    };
static mut l_Lean_Level_normalize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Level_normalize___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_normalize___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_toResult___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Level_PP_toResult___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__1_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
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
static mut l_Lean_Level_PP_toResult___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__2_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__1_value)
                as *mut leanh::LeanObject,
            13286986945483979944 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__4_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [63, 117, 0],
    };
static mut l_Lean_Level_PP_toResult___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__4_value)
                as *mut leanh::LeanObject,
            13784598040954107364 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__6_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [95, 117, 110, 105, 113, 0],
    };
static mut l_Lean_Level_PP_toResult___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__6_value)
                as *mut leanh::LeanObject,
            3978731030111751661 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__8_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [63, 95, 109, 118, 97, 114, 0],
    };
static mut l_Lean_Level_PP_toResult___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__8_value)
                as *mut leanh::LeanObject,
            601732279143319601 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__9_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value:
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
    m_data: [40, 0],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value:
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
        l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [32, 43, 32, 0],
    };
static mut l_Lean_Level_PP_Result_format___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__2_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [109, 97, 120, 0],
    };
static mut l_Lean_Level_PP_Result_format___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [105, 109, 97, 120, 0],
    };
static mut l_Lean_Level_PP_Result_format___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__4_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__3_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [76, 101, 118, 101, 108, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut leanh::LeanObject,
            11423656342444823216 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__4_value)
                as *mut leanh::LeanObject,
            16533827001853265987 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Level_PP_Result_quote___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__8_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [97, 100, 100, 76, 105, 116, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut leanh::LeanObject,
            11423656342444823216 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__8_value)
                as *mut leanh::LeanObject,
            12560806670959244085 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__10_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [43, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__10_value)
        as *mut leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut leanh::LeanObject,
            11423656342444823216 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__11_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
                as *mut leanh::LeanObject,
            7017890982578468202 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__13_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Level_PP_Result_quote___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__14_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__13_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut leanh::LeanObject,
            11423656342444823216 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
                as *mut leanh::LeanObject,
            2051294913818044796 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_instToFormat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_instToFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instToFormat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_instToFormat___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_Level_instToFormat___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instToFormat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Level_instToFormat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_instToString___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_Level_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Level_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Level_instQuoteMkStr1___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_Level_instQuoteMkStr1___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instQuoteMkStr1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instQuoteMkStr1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Level_instQuoteMkStr1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instQuoteMkStr1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46,
        48, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 117, 112, 100, 97, 116, 101, 83,
        117, 99, 99, 33, 73, 109, 112, 108, 0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value:
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
        115, 117, 99, 99, 32, 108, 101, 118, 101, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46,
        48, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 117, 112, 100, 97, 116, 101, 77,
        97, 120, 33, 73, 109, 112, 108, 0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        109, 97, 120, 32, 108, 101, 118, 101, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value:
    leanh::LeanStringObject<49> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 49,
    m_capacity: 49,
    m_length: 48,
    m_data: [
        95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46,
        48, 46, 76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 117, 112, 100, 97, 116, 101, 73,
        77, 97, 120, 33, 73, 109, 112, 108, 0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value:
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
        105, 109, 97, 120, 32, 108, 101, 118, 101, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100,
        0,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_imax(
    mut v_n_2669_: *mut leanh::LeanObject,
    mut v_m_2670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    v___x_2671_ = leanh::lean_unsigned_to_nat(0);
    v___x_2672_ = lean_nat_dec_eq(v_m_2670_, v___x_2671_);
    if v___x_2672_ == 0 {
        let mut v___x_2673_: u8 = 0;
        v___x_2673_ = lean_nat_dec_le(v_n_2669_, v_m_2670_);
        if v___x_2673_ == 0 {
            leanh::lean_inc(v_n_2669_);
            return v_n_2669_;
        } else {
            leanh::lean_inc(v_m_2670_);
            return v_m_2670_;
        }
    } else {
        return v___x_2671_;
    }
}
pub unsafe fn l_Nat_imax___boxed(
    mut v_n_2674_: *mut leanh::LeanObject,
    mut v_m_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Nat_imax(v_n_2674_, v_m_2675_);
    leanh::lean_dec(v_m_2675_);
    leanh::lean_dec(v_n_2674_);
    return v_res_2676_;
}
pub unsafe fn _init_l_Lean_instInhabitedData___aux__1___closed__0() -> u64 {
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u64 = 0;
    v___x_2677_ = leanh::lean_unsigned_to_nat(0);
    v___x_2678_ = lean_uint64_of_nat(v___x_2677_);
    return v___x_2678_;
}
pub unsafe fn _init_l_Lean_instInhabitedData___aux__1() -> u64 {
    let mut v___x_2679_: u64 = 0;
    v___x_2679_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0_once),
        _init_l_Lean_instInhabitedData___aux__1___closed__0,
    );
    return v___x_2679_;
}
pub unsafe fn _init_l_Lean_instInhabitedData() -> u64 {
    let mut v___x_2680_: u64 = 0;
    v___x_2680_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0_once),
        _init_l_Lean_instInhabitedData___aux__1___closed__0,
    );
    return v___x_2680_;
}
pub unsafe fn l_Lean_Level_Data_hash(mut v_c_2681_: u64) -> u64 {
    let mut v___x_2682_: u32 = 0;
    let mut v___x_2683_: u64 = 0;
    v___x_2682_ = lean_uint64_to_uint32(v_c_2681_);
    v___x_2683_ = lean_uint32_to_uint64(v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_Level_Data_hash___boxed(
    mut v_c_2684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2685_: u64 = 0;
    let mut v_res_2686_: u64 = 0;
    let mut v_r_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2685_ = leanh::lean_unbox_uint64(v_c_2684_);
    leanh::lean_dec_ref(v_c_2684_);
    v_res_2686_ = l_Lean_Level_Data_hash(v_c_boxed_2685_);
    v_r_2687_ = leanh::lean_box_uint64(v_res_2686_);
    return v_r_2687_;
}
pub unsafe fn l_Lean_Level_Data_depth(mut v_c_2690_: u64) -> u32 {
    let mut v___x_2691_: u64 = 0;
    let mut v___x_2692_: u64 = 0;
    let mut v___x_2693_: u32 = 0;
    v___x_2691_ = 40u64;
    v___x_2692_ = lean_uint64_shift_right(v_c_2690_, v___x_2691_);
    v___x_2693_ = lean_uint64_to_uint32(v___x_2692_);
    return v___x_2693_;
}
pub unsafe fn l_Lean_Level_Data_depth___boxed(
    mut v_c_2694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2695_: u64 = 0;
    let mut v_res_2696_: u32 = 0;
    let mut v_r_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2695_ = leanh::lean_unbox_uint64(v_c_2694_);
    leanh::lean_dec_ref(v_c_2694_);
    v_res_2696_ = l_Lean_Level_Data_depth(v_c_boxed_2695_);
    v_r_2697_ = leanh::lean_box_uint32(v_res_2696_);
    return v_r_2697_;
}
pub unsafe fn l_Lean_Level_Data_hasMVar(mut v_c_2698_: u64) -> u8 {
    let mut v___x_2699_: u64 = 0;
    let mut v___x_2700_: u64 = 0;
    let mut v___x_2701_: u64 = 0;
    let mut v___x_2702_: u64 = 0;
    let mut v___x_2703_: u8 = 0;
    v___x_2699_ = 32u64;
    v___x_2700_ = lean_uint64_shift_right(v_c_2698_, v___x_2699_);
    v___x_2701_ = 1u64;
    v___x_2702_ = lean_uint64_land(v___x_2700_, v___x_2701_);
    v___x_2703_ = lean_uint64_dec_eq(v___x_2702_, v___x_2701_);
    return v___x_2703_;
}
pub unsafe fn l_Lean_Level_Data_hasMVar___boxed(
    mut v_c_2704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2705_: u64 = 0;
    let mut v_res_2706_: u8 = 0;
    let mut v_r_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2705_ = leanh::lean_unbox_uint64(v_c_2704_);
    leanh::lean_dec_ref(v_c_2704_);
    v_res_2706_ = l_Lean_Level_Data_hasMVar(v_c_boxed_2705_);
    v_r_2707_ = leanh::lean_box((v_res_2706_) as usize);
    return v_r_2707_;
}
pub unsafe fn l_Lean_Level_Data_hasParam(mut v_c_2708_: u64) -> u8 {
    let mut v___x_2709_: u64 = 0;
    let mut v___x_2710_: u64 = 0;
    let mut v___x_2711_: u64 = 0;
    let mut v___x_2712_: u64 = 0;
    let mut v___x_2713_: u8 = 0;
    v___x_2709_ = 33u64;
    v___x_2710_ = lean_uint64_shift_right(v_c_2708_, v___x_2709_);
    v___x_2711_ = 1u64;
    v___x_2712_ = lean_uint64_land(v___x_2710_, v___x_2711_);
    v___x_2713_ = lean_uint64_dec_eq(v___x_2712_, v___x_2711_);
    return v___x_2713_;
}
pub unsafe fn l_Lean_Level_Data_hasParam___boxed(
    mut v_c_2714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2715_: u64 = 0;
    let mut v_res_2716_: u8 = 0;
    let mut v_r_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2715_ = leanh::lean_unbox_uint64(v_c_2714_);
    leanh::lean_dec_ref(v_c_2714_);
    v_res_2716_ = l_Lean_Level_Data_hasParam(v_c_boxed_2715_);
    v_r_2717_ = leanh::lean_box((v_res_2716_) as usize);
    return v_r_2717_;
}
pub unsafe fn l_Lean_Level_mkData___boxed(
    mut v_h_2722_: *mut leanh::LeanObject,
    mut v_depth_2723_: *mut leanh::LeanObject,
    mut v_hasMVar_2724_: *mut leanh::LeanObject,
    mut v_hasParam_2725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_h_boxed_2726_: u64 = 0;
    let mut v_hasMVar_boxed_2727_: u8 = 0;
    let mut v_hasParam_boxed_2728_: u8 = 0;
    let mut v_res_2729_: u64 = 0;
    let mut v_r_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_2726_ = leanh::lean_unbox_uint64(v_h_2722_);
    leanh::lean_dec_ref(v_h_2722_);
    v_hasMVar_boxed_2727_ = (leanh::lean_unbox(v_hasMVar_2724_) as u8);
    v_hasParam_boxed_2728_ = (leanh::lean_unbox(v_hasParam_2725_) as u8);
    v_res_2729_ = lean_level_mk_data(
        v_h_boxed_2726_,
        v_depth_2723_,
        v_hasMVar_boxed_2727_,
        v_hasParam_boxed_2728_,
    );
    v_r_2730_ = leanh::lean_box_uint64(v_res_2729_);
    return v_r_2730_;
}
pub unsafe fn l_Lean_instReprData___lam__0(
    mut v_v_2738_: u64,
    mut v_prec_2739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u64 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u32 = 0;
    let mut v___x_2776_: u32 = 0;
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2770_ = l_Lean_instReprData___lam__0___closed__5;
                v___x_2771_ = l_Lean_Level_Data_hash(v_v_2738_);
                v___x_2772_ = lean_uint64_to_nat(v___x_2771_);
                v___x_2773_ = l_Nat_reprFast(v___x_2772_);
                v_r_2774_ = lean_string_append(v___x_2770_, v___x_2773_);
                leanh::lean_dec_ref(v___x_2773_);
                v___x_2775_ = l_Lean_Level_Data_depth(v_v_2738_);
                v___x_2776_ = 0;
                v___x_2777_ = lean_uint32_dec_eq(v___x_2775_, v___x_2776_);
                if v___x_2777_ == 0 {
                    v___x_2778_ = l_Lean_instReprData___lam__0___closed__6;
                    v___x_2779_ = lean_string_append(v_r_2774_, v___x_2778_);
                    v___x_2780_ = lean_uint32_to_nat(v___x_2775_);
                    v___x_2781_ = l_Nat_reprFast(v___x_2780_);
                    v___x_2782_ = lean_string_append(v___x_2779_, v___x_2781_);
                    leanh::lean_dec_ref(v___x_2781_);
                    v___x_2783_ = l_Lean_instReprData___lam__0___closed__0;
                    v_r_2784_ = lean_string_append(v___x_2782_, v___x_2783_);
                    v_r_2764_ = v_r_2784_;
                    state = 5;
                    continue;
                } else {
                    v_r_2764_ = v_r_2774_;
                    state = 5;
                    continue;
                }
            }
            1 => {
                v___x_2742_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2742_, 0, v_r_2741_);
                v___x_2743_ = l_Repr_addAppParen(v___x_2742_, v_prec_2739_);
                return v___x_2743_;
            }
            2 => {
                v___x_2747_ = lean_string_append(v___y_2745_, v___y_2746_);
                v___x_2748_ = l_Lean_instReprData___lam__0___closed__0;
                v_r_2749_ = lean_string_append(v___x_2747_, v___x_2748_);
                v_r_2741_ = v_r_2749_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2752_ = l_Lean_Level_Data_hasParam(v_v_2738_);
                if v___x_2752_ == 0 {
                    v_r_2741_ = v_r_2751_;
                    state = 1;
                    continue;
                } else {
                    v___x_2753_ = l_Lean_instReprData___lam__0___closed__1;
                    v___x_2754_ = lean_string_append(v_r_2751_, v___x_2753_);
                    if v___x_2752_ == 0 {
                        v___x_2755_ = l_Lean_instReprData___lam__0___closed__2;
                        v___y_2745_ = v___x_2754_;
                        v___y_2746_ = v___x_2755_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2756_ = l_Lean_instReprData___lam__0___closed__3;
                        v___y_2745_ = v___x_2754_;
                        v___y_2746_ = v___x_2756_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2760_ = lean_string_append(v___y_2758_, v___y_2759_);
                v___x_2761_ = l_Lean_instReprData___lam__0___closed__0;
                v_r_2762_ = lean_string_append(v___x_2760_, v___x_2761_);
                v_r_2751_ = v_r_2762_;
                state = 3;
                continue;
            }
            5 => {
                v___x_2765_ = l_Lean_Level_Data_hasMVar(v_v_2738_);
                if v___x_2765_ == 0 {
                    v_r_2751_ = v_r_2764_;
                    state = 3;
                    continue;
                } else {
                    v___x_2766_ = l_Lean_instReprData___lam__0___closed__4;
                    v___x_2767_ = lean_string_append(v_r_2764_, v___x_2766_);
                    if v___x_2765_ == 0 {
                        v___x_2768_ = l_Lean_instReprData___lam__0___closed__2;
                        v___y_2758_ = v___x_2767_;
                        v___y_2759_ = v___x_2768_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2769_ = l_Lean_instReprData___lam__0___closed__3;
                        v___y_2758_ = v___x_2767_;
                        v___y_2759_ = v___x_2769_;
                        state = 4;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprData___lam__0___boxed(
    mut v_v_2785_: *mut leanh::LeanObject,
    mut v_prec_2786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_2787_: u64 = 0;
    let mut v_res_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2787_ = leanh::lean_unbox_uint64(v_v_2785_);
    leanh::lean_dec_ref(v_v_2785_);
    v_res_2788_ = l_Lean_instReprData___lam__0(v_v_boxed_2787_, v_prec_2786_);
    leanh::lean_dec(v_prec_2786_);
    return v_res_2788_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevelMVarId_default() -> *mut leanh::LeanObject {
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = leanh::lean_box(0);
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevelMVarId() -> *mut leanh::LeanObject {
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = leanh::lean_box(0);
    return v___x_2792_;
}
pub unsafe fn l_Lean_instBEqLevelMVarId_beq(
    mut v_x_2793_: *mut leanh::LeanObject,
    mut v_x_2794_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2795_: u8 = 0;
    v___x_2795_ = lean_name_eq(v_x_2793_, v_x_2794_);
    return v___x_2795_;
}
pub unsafe fn l_Lean_instBEqLevelMVarId_beq___boxed(
    mut v_x_2796_: *mut leanh::LeanObject,
    mut v_x_2797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_instBEqLevelMVarId_beq(v_x_2796_, v_x_2797_);
    leanh::lean_dec(v_x_2797_);
    leanh::lean_dec(v_x_2796_);
    v_r_2799_ = leanh::lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn _init_l_Lean_instHashableLevelMVarId_hash___closed__0() -> u64 {
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u64 = 0;
    v___x_2802_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2803_ = lean_uint64_of_nat(v___x_2802_);
    return v___x_2803_;
}
pub unsafe fn _init_l_Lean_instHashableLevelMVarId_hash___closed__1() -> u64 {
    let mut v___x_2804_: u64 = 0;
    let mut v___x_2805_: u64 = 0;
    let mut v___x_2806_: u64 = 0;
    v___x_2804_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__0_once),
        _init_l_Lean_instHashableLevelMVarId_hash___closed__0,
    );
    v___x_2805_ = 0u64;
    v___x_2806_ = lean_uint64_mix_hash(v___x_2805_, v___x_2804_);
    return v___x_2806_;
}
pub unsafe fn l_Lean_instHashableLevelMVarId_hash(
    mut v_x_2807_: *mut leanh::LeanObject,
) -> u64 {
    let mut v___x_2808_: u64 = 0;
    v___x_2808_ = 0u64;
    if leanh::lean_obj_tag(v_x_2807_) == 0 {
        let mut v___x_2809_: u64 = 0;
        v___x_2809_ = leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__1),
            core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__1_once),
            _init_l_Lean_instHashableLevelMVarId_hash___closed__1,
        );
        return v___x_2809_;
    } else {
        let mut v_hash_2810_: u64 = 0;
        let mut v___x_2811_: u64 = 0;
        v_hash_2810_ = leanh::lean_ctor_get_uint64(
            v_x_2807_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        );
        v___x_2811_ = lean_uint64_mix_hash(v___x_2808_, v_hash_2810_);
        return v___x_2811_;
    }
}
pub unsafe fn l_Lean_instHashableLevelMVarId_hash___boxed(
    mut v_x_2812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2813_: u64 = 0;
    let mut v_r_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Lean_instHashableLevelMVarId_hash(v_x_2812_);
    leanh::lean_dec(v_x_2812_);
    v_r_2814_ = leanh::lean_box_uint64(v_res_2813_);
    return v_r_2814_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(
    mut v_a_2817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = lean_nat_to_int(v_a_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = leanh::lean_unsigned_to_nat(8);
    v___x_2833_ = lean_nat_to_int(v___x_2832_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__0;
    v___x_2836_ = lean_string_length(v___x_2835_);
    return v___x_2836_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2837_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9,
    );
    v___x_2838_ = lean_nat_to_int(v___x_2837_);
    return v___x_2838_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr___redArg(
    mut v_x_2843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__6;
    v___x_2845_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7,
    );
    v___x_2846_ = leanh::lean_unsigned_to_nat(0);
    v___x_2847_ = l_Lean_Name_reprPrec(v_x_2843_, v___x_2846_);
    v___x_2848_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2848_, 0, v___x_2845_);
    leanh::lean_ctor_set(v___x_2848_, 1, v___x_2847_);
    v___x_2849_ = 0;
    v___x_2850_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2850_, 0, v___x_2848_);
    leanh::lean_ctor_set_uint8(
        v___x_2850_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2849_,
    );
    v___x_2851_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2851_, 0, v___x_2844_);
    leanh::lean_ctor_set(v___x_2851_, 1, v___x_2850_);
    v___x_2852_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10,
    );
    v___x_2853_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__11;
    v___x_2854_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2854_, 0, v___x_2853_);
    leanh::lean_ctor_set(v___x_2854_, 1, v___x_2851_);
    v___x_2855_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__12;
    v___x_2856_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2856_, 0, v___x_2854_);
    leanh::lean_ctor_set(v___x_2856_, 1, v___x_2855_);
    v___x_2857_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2857_, 0, v___x_2852_);
    leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
    v___x_2858_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_2858_, 0, v___x_2857_);
    leanh::lean_ctor_set_uint8(
        v___x_2858_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_2849_,
    );
    return v___x_2858_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr(
    mut v_x_2859_: *mut leanh::LeanObject,
    mut v_prec_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_2859_);
    return v___x_2861_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr___boxed(
    mut v_x_2862_: *mut leanh::LeanObject,
    mut v_prec_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_instReprLevelMVarId_repr(v_x_2862_, v_prec_2863_);
    leanh::lean_dec(v_prec_2863_);
    return v_res_2864_;
}
pub unsafe fn _init_l_Lean_instInhabitedLMVarIdSet___aux__1() -> *mut leanh::LeanObject {
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = leanh::lean_box(1);
    return v___x_2869_;
}
pub unsafe fn _init_l_Lean_instInhabitedLMVarIdSet() -> *mut leanh::LeanObject {
    let mut v___x_2870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ = leanh::lean_box(1);
    return v___x_2870_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1() -> *mut leanh::LeanObject
{
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = leanh::lean_box(1);
    return v___x_2871_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLMVarIdSet() -> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = leanh::lean_box(1);
    return v___x_2872_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(
    mut v_f_2873_: *mut leanh::LeanObject,
    mut v_a_2874_: *mut leanh::LeanObject,
    mut v_b_2875_: *mut leanh::LeanObject,
    mut v_c_2876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ = leanh::lean_apply_2(v_f_2873_, v_a_2874_, v_c_2876_);
    return v___x_2877_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(
    mut v_toPure_2878_: *mut leanh::LeanObject,
    mut v_____do__lift_2879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_2880_ = leanh::lean_ctor_get(v_____do__lift_2879_, 0);
    leanh::lean_inc(v_a_2880_);
    leanh::lean_dec_ref(v_____do__lift_2879_);
    v___x_2881_ = leanh::lean_apply_2(v_toPure_2878_, leanh::lean_box(0), v_a_2880_);
    return v___x_2881_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(
    mut v_inst_2882_: *mut leanh::LeanObject,
    mut v_m_2883_: *mut leanh::LeanObject,
    mut v_init_2884_: *mut leanh::LeanObject,
    mut v_f_2885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2886_ = leanh::lean_ctor_get(v_inst_2882_, 0);
    v_toBind_2887_ = leanh::lean_ctor_get(v_inst_2882_, 1);
    leanh::lean_inc(v_toBind_2887_);
    v_toPure_2888_ = leanh::lean_ctor_get(v_toApplicative_2886_, 1);
    leanh::lean_inc(v_toPure_2888_);
    v___f_2889_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2889_, 0, v_f_2885_);
    v___x_2890_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2882_,
        v___f_2889_,
        v_init_2884_,
        v_m_2883_,
    );
    v___f_2891_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2891_, 0, v_toPure_2888_);
    v___x_2892_ = leanh::lean_apply_4(
        v_toBind_2887_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2890_,
        v___f_2891_,
    );
    return v___x_2892_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(
    mut v_m_2893_: *mut leanh::LeanObject,
    mut v_inst_2894_: *mut leanh::LeanObject,
    mut v_00_u03b2_2895_: *mut leanh::LeanObject,
    mut v_m_2896_: *mut leanh::LeanObject,
    mut v_init_2897_: *mut leanh::LeanObject,
    mut v_f_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2899_ = leanh::lean_ctor_get(v_inst_2894_, 0);
    v_toBind_2900_ = leanh::lean_ctor_get(v_inst_2894_, 1);
    leanh::lean_inc(v_toBind_2900_);
    v_toPure_2901_ = leanh::lean_ctor_get(v_toApplicative_2899_, 1);
    leanh::lean_inc(v_toPure_2901_);
    v___f_2902_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2902_, 0, v_f_2898_);
    v___x_2903_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2894_,
        v___f_2902_,
        v_init_2897_,
        v_m_2896_,
    );
    v___f_2904_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2904_, 0, v_toPure_2901_);
    v___x_2905_ = leanh::lean_apply_4(
        v_toBind_2900_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2903_,
        v___f_2904_,
    );
    return v___x_2905_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(
    mut v_inst_2906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___x_2907_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2907_, 1, v_inst_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad(
    mut v_m_2908_: *mut leanh::LeanObject,
    mut v_inst_2909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    leanh::lean_closure_set(v___x_2910_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2910_, 1, v_inst_2909_);
    return v___x_2910_;
}
pub unsafe fn l_Lean_instEmptyCollectionLMVarIdMap___aux__1(
    mut v_00_u03b1_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = leanh::lean_box(1);
    return v___x_2912_;
}
pub unsafe fn l_Lean_instEmptyCollectionLMVarIdMap(
    mut v_00_u03b1_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = leanh::lean_box(1);
    return v___x_2914_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(
    mut v_f_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
    mut v_b_2917_: *mut leanh::LeanObject,
    mut v_c_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2919_, 0, v_a_2916_);
    leanh::lean_ctor_set(v___x_2919_, 1, v_b_2917_);
    v___x_2920_ = leanh::lean_apply_2(v_f_2915_, v___x_2919_, v_c_2918_);
    return v___x_2920_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(
    mut v_inst_2921_: *mut leanh::LeanObject,
    mut v_m_2922_: *mut leanh::LeanObject,
    mut v_init_2923_: *mut leanh::LeanObject,
    mut v_f_2924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2925_ = leanh::lean_ctor_get(v_inst_2921_, 0);
    v_toBind_2926_ = leanh::lean_ctor_get(v_inst_2921_, 1);
    leanh::lean_inc(v_toBind_2926_);
    v_toPure_2927_ = leanh::lean_ctor_get(v_toApplicative_2925_, 1);
    leanh::lean_inc(v_toPure_2927_);
    v___f_2928_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2928_, 0, v_f_2924_);
    v___x_2929_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2921_,
        v___f_2928_,
        v_init_2923_,
        v_m_2922_,
    );
    v___f_2930_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2930_, 0, v_toPure_2927_);
    v___x_2931_ = leanh::lean_apply_4(
        v_toBind_2926_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2929_,
        v___f_2930_,
    );
    return v___x_2931_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(
    mut v_m_2932_: *mut leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut leanh::LeanObject,
    mut v_inst_2934_: *mut leanh::LeanObject,
    mut v_00_u03b2_2935_: *mut leanh::LeanObject,
    mut v_m_2936_: *mut leanh::LeanObject,
    mut v_init_2937_: *mut leanh::LeanObject,
    mut v_f_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2939_ = leanh::lean_ctor_get(v_inst_2934_, 0);
    v_toBind_2940_ = leanh::lean_ctor_get(v_inst_2934_, 1);
    leanh::lean_inc(v_toBind_2940_);
    v_toPure_2941_ = leanh::lean_ctor_get(v_toApplicative_2939_, 1);
    leanh::lean_inc(v_toPure_2941_);
    v___f_2942_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2942_, 0, v_f_2938_);
    v___x_2943_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2934_,
        v___f_2942_,
        v_init_2937_,
        v_m_2936_,
    );
    v___f_2944_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2944_, 0, v_toPure_2941_);
    v___x_2945_ = leanh::lean_apply_4(
        v_toBind_2940_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2943_,
        v___f_2944_,
    );
    return v___x_2945_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(
    mut v_inst_2946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___x_2947_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2947_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2947_, 2, v_inst_2946_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(
    mut v_m_2948_: *mut leanh::LeanObject,
    mut v_00_u03b1_2949_: *mut leanh::LeanObject,
    mut v_inst_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___x_2951_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2951_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2951_, 2, v_inst_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Lean_instInhabitedLMVarIdMap(
    mut v_00_u03b1_2952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = leanh::lean_box(1);
    return v___x_2953_;
}
pub unsafe fn l_Lean_Level_ctorIdx(
    mut v_x_2954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2954_) {
        0 => {
            let mut v___x_2955_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2955_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2955_;
        }
        1 => {
            let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2956_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2956_;
        }
        2 => {
            let mut v___x_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2957_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2957_;
        }
        3 => {
            let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2958_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2958_;
        }
        4 => {
            let mut v___x_2959_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2959_ = leanh::lean_unsigned_to_nat(4);
            return v___x_2959_;
        }
        _ => {
            let mut v___x_2960_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2960_ = leanh::lean_unsigned_to_nat(5);
            return v___x_2960_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorIdx___boxed(
    mut v_x_2961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2962_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Level_ctorIdx(v_x_2961_);
    leanh::lean_dec(v_x_2961_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Level_ctorElim___redArg(
    mut v_t_2963_: *mut leanh::LeanObject,
    mut v_k_2964_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2963_) {
        0 => {
            return v_k_2964_;
        }
        2 => {
            let mut v_a_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2965_ = leanh::lean_ctor_get(v_t_2963_, 0);
            leanh::lean_inc(v_a_2965_);
            v_a_2966_ = leanh::lean_ctor_get(v_t_2963_, 1);
            leanh::lean_inc(v_a_2966_);
            leanh::lean_dec_ref_known(v_t_2963_, 2);
            v___x_2967_ = leanh::lean_apply_2(v_k_2964_, v_a_2965_, v_a_2966_);
            return v___x_2967_;
        }
        3 => {
            let mut v_a_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2968_ = leanh::lean_ctor_get(v_t_2963_, 0);
            leanh::lean_inc(v_a_2968_);
            v_a_2969_ = leanh::lean_ctor_get(v_t_2963_, 1);
            leanh::lean_inc(v_a_2969_);
            leanh::lean_dec_ref_known(v_t_2963_, 2);
            v___x_2970_ = leanh::lean_apply_2(v_k_2964_, v_a_2968_, v_a_2969_);
            return v___x_2970_;
        }
        _ => {
            let mut v_a_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2971_ = leanh::lean_ctor_get(v_t_2963_, 0);
            leanh::lean_inc(v_a_2971_);
            leanh::lean_dec(v_t_2963_);
            v___x_2972_ = leanh::lean_apply_1(v_k_2964_, v_a_2971_);
            return v___x_2972_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorElim(
    mut v_motive_2973_: *mut leanh::LeanObject,
    mut v_ctorIdx_2974_: *mut leanh::LeanObject,
    mut v_t_2975_: *mut leanh::LeanObject,
    mut v_h_2976_: *mut leanh::LeanObject,
    mut v_k_2977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2978_ = l_Lean_Level_ctorElim___redArg(v_t_2975_, v_k_2977_);
    return v___x_2978_;
}
pub unsafe fn l_Lean_Level_ctorElim___boxed(
    mut v_motive_2979_: *mut leanh::LeanObject,
    mut v_ctorIdx_2980_: *mut leanh::LeanObject,
    mut v_t_2981_: *mut leanh::LeanObject,
    mut v_h_2982_: *mut leanh::LeanObject,
    mut v_k_2983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_Lean_Level_ctorElim(
        v_motive_2979_,
        v_ctorIdx_2980_,
        v_t_2981_,
        v_h_2982_,
        v_k_2983_,
    );
    leanh::lean_dec(v_ctorIdx_2980_);
    return v_res_2984_;
}
pub unsafe fn l_Lean_Level_zero_elim___redArg(
    mut v_t_2985_: *mut leanh::LeanObject,
    mut v_zero_2986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Lean_Level_ctorElim___redArg(v_t_2985_, v_zero_2986_);
    return v___x_2987_;
}
pub unsafe fn l_Lean_Level_zero_elim(
    mut v_motive_2988_: *mut leanh::LeanObject,
    mut v_t_2989_: *mut leanh::LeanObject,
    mut v_h_2990_: *mut leanh::LeanObject,
    mut v_zero_2991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = l_Lean_Level_ctorElim___redArg(v_t_2989_, v_zero_2991_);
    return v___x_2992_;
}
pub unsafe fn l_Lean_Level_succ_elim___redArg(
    mut v_t_2993_: *mut leanh::LeanObject,
    mut v_succ_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = l_Lean_Level_ctorElim___redArg(v_t_2993_, v_succ_2994_);
    return v___x_2995_;
}
pub unsafe fn l_Lean_Level_succ_elim(
    mut v_motive_2996_: *mut leanh::LeanObject,
    mut v_t_2997_: *mut leanh::LeanObject,
    mut v_h_2998_: *mut leanh::LeanObject,
    mut v_succ_2999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3000_ = l_Lean_Level_ctorElim___redArg(v_t_2997_, v_succ_2999_);
    return v___x_3000_;
}
pub unsafe fn l_Lean_Level_max_elim___redArg(
    mut v_t_3001_: *mut leanh::LeanObject,
    mut v_max_3002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3003_ = l_Lean_Level_ctorElim___redArg(v_t_3001_, v_max_3002_);
    return v___x_3003_;
}
pub unsafe fn l_Lean_Level_max_elim(
    mut v_motive_3004_: *mut leanh::LeanObject,
    mut v_t_3005_: *mut leanh::LeanObject,
    mut v_h_3006_: *mut leanh::LeanObject,
    mut v_max_3007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Level_ctorElim___redArg(v_t_3005_, v_max_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Lean_Level_imax_elim___redArg(
    mut v_t_3009_: *mut leanh::LeanObject,
    mut v_imax_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Lean_Level_ctorElim___redArg(v_t_3009_, v_imax_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Lean_Level_imax_elim(
    mut v_motive_3012_: *mut leanh::LeanObject,
    mut v_t_3013_: *mut leanh::LeanObject,
    mut v_h_3014_: *mut leanh::LeanObject,
    mut v_imax_3015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_Level_ctorElim___redArg(v_t_3013_, v_imax_3015_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_Level_param_elim___redArg(
    mut v_t_3017_: *mut leanh::LeanObject,
    mut v_param_3018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3019_ = l_Lean_Level_ctorElim___redArg(v_t_3017_, v_param_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_Level_param_elim(
    mut v_motive_3020_: *mut leanh::LeanObject,
    mut v_t_3021_: *mut leanh::LeanObject,
    mut v_h_3022_: *mut leanh::LeanObject,
    mut v_param_3023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_Level_ctorElim___redArg(v_t_3021_, v_param_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Level_mvar_elim___redArg(
    mut v_t_3025_: *mut leanh::LeanObject,
    mut v_mvar_3026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_Level_ctorElim___redArg(v_t_3025_, v_mvar_3026_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_Level_mvar_elim(
    mut v_motive_3028_: *mut leanh::LeanObject,
    mut v_t_3029_: *mut leanh::LeanObject,
    mut v_h_3030_: *mut leanh::LeanObject,
    mut v_mvar_3031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Level_ctorElim___redArg(v_t_3029_, v_mvar_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Level_casesOn___override___redArg(
    mut v_t_3033_: *mut leanh::LeanObject,
    mut v_zero_3034_: *mut leanh::LeanObject,
    mut v_succ_3035_: *mut leanh::LeanObject,
    mut v_max_3036_: *mut leanh::LeanObject,
    mut v_imax_3037_: *mut leanh::LeanObject,
    mut v_param_3038_: *mut leanh::LeanObject,
    mut v_mvar_3039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3033_) {
        0 => {
            leanh::lean_dec(v_mvar_3039_);
            leanh::lean_dec(v_param_3038_);
            leanh::lean_dec(v_imax_3037_);
            leanh::lean_dec(v_max_3036_);
            leanh::lean_dec(v_succ_3035_);
            leanh::lean_inc(v_zero_3034_);
            return v_zero_3034_;
        }
        1 => {
            let mut v_a_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3039_);
            leanh::lean_dec(v_param_3038_);
            leanh::lean_dec(v_imax_3037_);
            leanh::lean_dec(v_max_3036_);
            v_a_3040_ = leanh::lean_ctor_get(v_t_3033_, 0);
            leanh::lean_inc(v_a_3040_);
            leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3041_ = leanh::lean_apply_1(v_succ_3035_, v_a_3040_);
            return v___x_3041_;
        }
        2 => {
            let mut v_a_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3039_);
            leanh::lean_dec(v_param_3038_);
            leanh::lean_dec(v_imax_3037_);
            leanh::lean_dec(v_succ_3035_);
            v_a_3042_ = leanh::lean_ctor_get(v_t_3033_, 0);
            leanh::lean_inc(v_a_3042_);
            v_a_3043_ = leanh::lean_ctor_get(v_t_3033_, 1);
            leanh::lean_inc(v_a_3043_);
            leanh::lean_dec_ref_known(v_t_3033_, 2);
            v___x_3044_ = leanh::lean_apply_2(v_max_3036_, v_a_3042_, v_a_3043_);
            return v___x_3044_;
        }
        3 => {
            let mut v_a_3045_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3039_);
            leanh::lean_dec(v_param_3038_);
            leanh::lean_dec(v_max_3036_);
            leanh::lean_dec(v_succ_3035_);
            v_a_3045_ = leanh::lean_ctor_get(v_t_3033_, 0);
            leanh::lean_inc(v_a_3045_);
            v_a_3046_ = leanh::lean_ctor_get(v_t_3033_, 1);
            leanh::lean_inc(v_a_3046_);
            leanh::lean_dec_ref_known(v_t_3033_, 2);
            v___x_3047_ = leanh::lean_apply_2(v_imax_3037_, v_a_3045_, v_a_3046_);
            return v___x_3047_;
        }
        4 => {
            let mut v_a_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3039_);
            leanh::lean_dec(v_imax_3037_);
            leanh::lean_dec(v_max_3036_);
            leanh::lean_dec(v_succ_3035_);
            v_a_3048_ = leanh::lean_ctor_get(v_t_3033_, 0);
            leanh::lean_inc(v_a_3048_);
            leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3049_ = leanh::lean_apply_1(v_param_3038_, v_a_3048_);
            return v___x_3049_;
        }
        _ => {
            let mut v_a_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_param_3038_);
            leanh::lean_dec(v_imax_3037_);
            leanh::lean_dec(v_max_3036_);
            leanh::lean_dec(v_succ_3035_);
            v_a_3050_ = leanh::lean_ctor_get(v_t_3033_, 0);
            leanh::lean_inc(v_a_3050_);
            leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3051_ = leanh::lean_apply_1(v_mvar_3039_, v_a_3050_);
            return v___x_3051_;
        }
    }
}
pub unsafe fn l_Lean_Level_casesOn___override___redArg___boxed(
    mut v_t_3052_: *mut leanh::LeanObject,
    mut v_zero_3053_: *mut leanh::LeanObject,
    mut v_succ_3054_: *mut leanh::LeanObject,
    mut v_max_3055_: *mut leanh::LeanObject,
    mut v_imax_3056_: *mut leanh::LeanObject,
    mut v_param_3057_: *mut leanh::LeanObject,
    mut v_mvar_3058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Lean_Level_casesOn___override___redArg(
        v_t_3052_,
        v_zero_3053_,
        v_succ_3054_,
        v_max_3055_,
        v_imax_3056_,
        v_param_3057_,
        v_mvar_3058_,
    );
    leanh::lean_dec(v_zero_3053_);
    return v_res_3059_;
}
pub unsafe fn l_Lean_Level_casesOn___override(
    mut v_motive_3060_: *mut leanh::LeanObject,
    mut v_t_3061_: *mut leanh::LeanObject,
    mut v_zero_3062_: *mut leanh::LeanObject,
    mut v_succ_3063_: *mut leanh::LeanObject,
    mut v_max_3064_: *mut leanh::LeanObject,
    mut v_imax_3065_: *mut leanh::LeanObject,
    mut v_param_3066_: *mut leanh::LeanObject,
    mut v_mvar_3067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_3061_) {
        0 => {
            leanh::lean_dec(v_mvar_3067_);
            leanh::lean_dec(v_param_3066_);
            leanh::lean_dec(v_imax_3065_);
            leanh::lean_dec(v_max_3064_);
            leanh::lean_dec(v_succ_3063_);
            leanh::lean_inc(v_zero_3062_);
            return v_zero_3062_;
        }
        1 => {
            let mut v_a_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3067_);
            leanh::lean_dec(v_param_3066_);
            leanh::lean_dec(v_imax_3065_);
            leanh::lean_dec(v_max_3064_);
            v_a_3068_ = leanh::lean_ctor_get(v_t_3061_, 0);
            leanh::lean_inc(v_a_3068_);
            leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3069_ = leanh::lean_apply_1(v_succ_3063_, v_a_3068_);
            return v___x_3069_;
        }
        2 => {
            let mut v_a_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3067_);
            leanh::lean_dec(v_param_3066_);
            leanh::lean_dec(v_imax_3065_);
            leanh::lean_dec(v_succ_3063_);
            v_a_3070_ = leanh::lean_ctor_get(v_t_3061_, 0);
            leanh::lean_inc(v_a_3070_);
            v_a_3071_ = leanh::lean_ctor_get(v_t_3061_, 1);
            leanh::lean_inc(v_a_3071_);
            leanh::lean_dec_ref_known(v_t_3061_, 2);
            v___x_3072_ = leanh::lean_apply_2(v_max_3064_, v_a_3070_, v_a_3071_);
            return v___x_3072_;
        }
        3 => {
            let mut v_a_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3067_);
            leanh::lean_dec(v_param_3066_);
            leanh::lean_dec(v_max_3064_);
            leanh::lean_dec(v_succ_3063_);
            v_a_3073_ = leanh::lean_ctor_get(v_t_3061_, 0);
            leanh::lean_inc(v_a_3073_);
            v_a_3074_ = leanh::lean_ctor_get(v_t_3061_, 1);
            leanh::lean_inc(v_a_3074_);
            leanh::lean_dec_ref_known(v_t_3061_, 2);
            v___x_3075_ = leanh::lean_apply_2(v_imax_3065_, v_a_3073_, v_a_3074_);
            return v___x_3075_;
        }
        4 => {
            let mut v_a_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_mvar_3067_);
            leanh::lean_dec(v_imax_3065_);
            leanh::lean_dec(v_max_3064_);
            leanh::lean_dec(v_succ_3063_);
            v_a_3076_ = leanh::lean_ctor_get(v_t_3061_, 0);
            leanh::lean_inc(v_a_3076_);
            leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3077_ = leanh::lean_apply_1(v_param_3066_, v_a_3076_);
            return v___x_3077_;
        }
        _ => {
            let mut v_a_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_param_3066_);
            leanh::lean_dec(v_imax_3065_);
            leanh::lean_dec(v_max_3064_);
            leanh::lean_dec(v_succ_3063_);
            v_a_3078_ = leanh::lean_ctor_get(v_t_3061_, 0);
            leanh::lean_inc(v_a_3078_);
            leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3079_ = leanh::lean_apply_1(v_mvar_3067_, v_a_3078_);
            return v___x_3079_;
        }
    }
}
pub unsafe fn l_Lean_Level_casesOn___override___boxed(
    mut v_motive_3080_: *mut leanh::LeanObject,
    mut v_t_3081_: *mut leanh::LeanObject,
    mut v_zero_3082_: *mut leanh::LeanObject,
    mut v_succ_3083_: *mut leanh::LeanObject,
    mut v_max_3084_: *mut leanh::LeanObject,
    mut v_imax_3085_: *mut leanh::LeanObject,
    mut v_param_3086_: *mut leanh::LeanObject,
    mut v_mvar_3087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3088_ = l_Lean_Level_casesOn___override(
        v_motive_3080_,
        v_t_3081_,
        v_zero_3082_,
        v_succ_3083_,
        v_max_3084_,
        v_imax_3085_,
        v_param_3086_,
        v_mvar_3087_,
    );
    leanh::lean_dec(v_zero_3082_);
    return v_res_3088_;
}
pub unsafe fn _init_l_Lean_Level_zero___override() -> *mut leanh::LeanObject {
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = leanh::lean_box(0);
    return v___x_3089_;
}
pub unsafe fn _init_l_Lean_Level_data___override___closed__0() -> u64 {
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u64 = 0;
    let mut v___x_3093_: u64 = 0;
    v___x_3090_ = 0;
    v___x_3091_ = leanh::lean_unsigned_to_nat(0);
    v___x_3092_ = 2221u64;
    v___x_3093_ = lean_level_mk_data(v___x_3092_, v___x_3091_, v___x_3090_, v___x_3090_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Level_data___override(mut v_x_3094_: *mut leanh::LeanObject) -> u64 {
    match leanh::lean_obj_tag(v_x_3094_) {
        0 => {
            let mut v___x_3095_: u64 = 0;
            v___x_3095_ = leanh::lean_uint64_once(
                core::ptr::addr_of_mut!(l_Lean_Level_data___override___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Level_data___override___closed__0_once),
                _init_l_Lean_Level_data___override___closed__0,
            );
            return v___x_3095_;
        }
        2 => {
            let mut v_data_3096_: u64 = 0;
            v_data_3096_ = leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_data_3096_;
        }
        3 => {
            let mut v_data_3097_: u64 = 0;
            v_data_3097_ = leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            );
            return v_data_3097_;
        }
        _ => {
            let mut v_data_3098_: u64 = 0;
            v_data_3098_ = leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            );
            return v_data_3098_;
        }
    }
}
pub unsafe fn l_Lean_Level_data___override___boxed(
    mut v_x_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3100_: u64 = 0;
    let mut v_r_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Lean_Level_data___override(v_x_3099_);
    leanh::lean_dec(v_x_3099_);
    v_r_3101_ = leanh::lean_box_uint64(v_res_3100_);
    return v_r_3101_;
}
pub unsafe fn l_Lean_Level_succ___override(
    mut v_a_3102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3103_: u64 = 0;
    let mut v___x_3104_: u64 = 0;
    let mut v___x_3105_: u64 = 0;
    let mut v___x_3106_: u64 = 0;
    let mut v___x_3107_: u32 = 0;
    let mut v___x_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: u64 = 0;
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3103_ = 2243u64;
    v___x_3104_ = l_Lean_Level_data___override(v_a_3102_);
    v___x_3105_ = l_Lean_Level_Data_hash(v___x_3104_);
    v___x_3106_ = lean_uint64_mix_hash(v___x_3103_, v___x_3105_);
    v___x_3107_ = l_Lean_Level_Data_depth(v___x_3104_);
    v___x_3108_ = lean_uint32_to_nat(v___x_3107_);
    v___x_3109_ = leanh::lean_unsigned_to_nat(1);
    v___x_3110_ = lean_nat_add(v___x_3108_, v___x_3109_);
    leanh::lean_dec(v___x_3108_);
    v___x_3111_ = l_Lean_Level_Data_hasMVar(v___x_3104_);
    v___x_3112_ = l_Lean_Level_Data_hasParam(v___x_3104_);
    v___x_3113_ = lean_level_mk_data(v___x_3106_, v___x_3110_, v___x_3111_, v___x_3112_);
    v___x_3114_ = leanh::lean_alloc_ctor(1, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_3114_, 0, v_a_3102_);
    leanh::lean_ctor_set_uint64(
        v___x_3114_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3113_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Level_max___override(
    mut v_a_3115_: *mut leanh::LeanObject,
    mut v_a_3116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3117_: u64 = 0;
    let mut v___x_3118_: u64 = 0;
    let mut v___x_3119_: u64 = 0;
    let mut v___x_3120_: u64 = 0;
    let mut v___x_3121_: u64 = 0;
    let mut v___x_3122_: u64 = 0;
    let mut v___x_3123_: u64 = 0;
    let mut v___y_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: u8 = 0;
    let mut v___y_3127_: u8 = 0;
    let mut v___x_3128_: u64 = 0;
    let mut v___x_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: u8 = 0;
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: u8 = 0;
    let mut v___y_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: u32 = 0;
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u32 = 0;
    let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3117_ = 2251u64;
                v___x_3118_ = l_Lean_Level_data___override(v_a_3115_);
                v___x_3119_ = l_Lean_Level_Data_hash(v___x_3118_);
                v___x_3120_ = l_Lean_Level_data___override(v_a_3116_);
                v___x_3121_ = l_Lean_Level_Data_hash(v___x_3120_);
                v___x_3122_ = lean_uint64_mix_hash(v___x_3119_, v___x_3121_);
                v___x_3123_ = lean_uint64_mix_hash(v___x_3117_, v___x_3122_);
                v___x_3141_ = l_Lean_Level_Data_depth(v___x_3118_);
                v___x_3142_ = lean_uint32_to_nat(v___x_3141_);
                v___x_3143_ = l_Lean_Level_Data_depth(v___x_3120_);
                v___x_3144_ = lean_uint32_to_nat(v___x_3143_);
                v___x_3145_ = lean_nat_dec_le(v___x_3142_, v___x_3144_);
                if v___x_3145_ == 0 {
                    leanh::lean_dec(v___x_3144_);
                    v___y_3136_ = v___x_3142_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3142_);
                    v___y_3136_ = v___x_3144_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3128_ =
                    lean_level_mk_data(v___x_3123_, v___y_3125_, v___y_3126_, v___y_3127_);
                v___x_3129_ = leanh::lean_alloc_ctor(2, 2, (8) as u32);
                leanh::lean_ctor_set(v___x_3129_, 0, v_a_3115_);
                leanh::lean_ctor_set(v___x_3129_, 1, v_a_3116_);
                leanh::lean_ctor_set_uint64(
                    v___x_3129_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3128_,
                );
                return v___x_3129_;
            }
            2 => {
                v___x_3133_ = l_Lean_Level_Data_hasParam(v___x_3118_);
                if v___x_3133_ == 0 {
                    v___x_3134_ = l_Lean_Level_Data_hasParam(v___x_3120_);
                    v___y_3125_ = v___y_3131_;
                    v___y_3126_ = v___y_3132_;
                    v___y_3127_ = v___x_3134_;
                    state = 1;
                    continue;
                } else {
                    v___y_3125_ = v___y_3131_;
                    v___y_3126_ = v___y_3132_;
                    v___y_3127_ = v___x_3133_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3137_ = leanh::lean_unsigned_to_nat(1);
                v___x_3138_ = lean_nat_add(v___y_3136_, v___x_3137_);
                leanh::lean_dec(v___y_3136_);
                v___x_3139_ = l_Lean_Level_Data_hasMVar(v___x_3118_);
                if v___x_3139_ == 0 {
                    v___x_3140_ = l_Lean_Level_Data_hasMVar(v___x_3120_);
                    v___y_3131_ = v___x_3138_;
                    v___y_3132_ = v___x_3140_;
                    state = 2;
                    continue;
                } else {
                    v___y_3131_ = v___x_3138_;
                    v___y_3132_ = v___x_3139_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_imax___override(
    mut v_a_3146_: *mut leanh::LeanObject,
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3148_: u64 = 0;
    let mut v___x_3149_: u64 = 0;
    let mut v___x_3150_: u64 = 0;
    let mut v___x_3151_: u64 = 0;
    let mut v___x_3152_: u64 = 0;
    let mut v___x_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v___y_3156_: u8 = 0;
    let mut v___y_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: u8 = 0;
    let mut v___x_3159_: u64 = 0;
    let mut v___x_3160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: u8 = 0;
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___y_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: u32 = 0;
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u32 = 0;
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3148_ = 2267u64;
                v___x_3149_ = l_Lean_Level_data___override(v_a_3146_);
                v___x_3150_ = l_Lean_Level_Data_hash(v___x_3149_);
                v___x_3151_ = l_Lean_Level_data___override(v_a_3147_);
                v___x_3152_ = l_Lean_Level_Data_hash(v___x_3151_);
                v___x_3153_ = lean_uint64_mix_hash(v___x_3150_, v___x_3152_);
                v___x_3154_ = lean_uint64_mix_hash(v___x_3148_, v___x_3153_);
                v___x_3172_ = l_Lean_Level_Data_depth(v___x_3149_);
                v___x_3173_ = lean_uint32_to_nat(v___x_3172_);
                v___x_3174_ = l_Lean_Level_Data_depth(v___x_3151_);
                v___x_3175_ = lean_uint32_to_nat(v___x_3174_);
                v___x_3176_ = lean_nat_dec_le(v___x_3173_, v___x_3175_);
                if v___x_3176_ == 0 {
                    leanh::lean_dec(v___x_3175_);
                    v___y_3167_ = v___x_3173_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_3173_);
                    v___y_3167_ = v___x_3175_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3159_ =
                    lean_level_mk_data(v___x_3154_, v___y_3157_, v___y_3156_, v___y_3158_);
                v___x_3160_ = leanh::lean_alloc_ctor(3, 2, (8) as u32);
                leanh::lean_ctor_set(v___x_3160_, 0, v_a_3146_);
                leanh::lean_ctor_set(v___x_3160_, 1, v_a_3147_);
                leanh::lean_ctor_set_uint64(
                    v___x_3160_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_3159_,
                );
                return v___x_3160_;
            }
            2 => {
                v___x_3164_ = l_Lean_Level_Data_hasParam(v___x_3149_);
                if v___x_3164_ == 0 {
                    v___x_3165_ = l_Lean_Level_Data_hasParam(v___x_3151_);
                    v___y_3156_ = v___y_3163_;
                    v___y_3157_ = v___y_3162_;
                    v___y_3158_ = v___x_3165_;
                    state = 1;
                    continue;
                } else {
                    v___y_3156_ = v___y_3163_;
                    v___y_3157_ = v___y_3162_;
                    v___y_3158_ = v___x_3164_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3168_ = leanh::lean_unsigned_to_nat(1);
                v___x_3169_ = lean_nat_add(v___y_3167_, v___x_3168_);
                leanh::lean_dec(v___y_3167_);
                v___x_3170_ = l_Lean_Level_Data_hasMVar(v___x_3149_);
                if v___x_3170_ == 0 {
                    v___x_3171_ = l_Lean_Level_Data_hasMVar(v___x_3151_);
                    v___y_3162_ = v___x_3169_;
                    v___y_3163_ = v___x_3171_;
                    state = 2;
                    continue;
                } else {
                    v___y_3162_ = v___x_3169_;
                    v___y_3163_ = v___x_3170_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_param___override(
    mut v_a_3177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3178_: u64 = 0;
    let mut v___y_3180_: u64 = 0;
    let mut v___x_3181_: u64 = 0;
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: u64 = 0;
    let mut v___x_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u64 = 0;
    let mut v_hash_3188_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3178_ = 2239u64;
                if leanh::lean_obj_tag(v_a_3177_) == 0 {
                    v___x_3187_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_instHashableLevelMVarId_hash___closed__0_once
                        ),
                        _init_l_Lean_instHashableLevelMVarId_hash___closed__0,
                    );
                    v___y_3180_ = v___x_3187_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3188_ = leanh::lean_ctor_get_uint64(
                        v_a_3177_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3180_ = v_hash_3188_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3181_ = lean_uint64_mix_hash(v___x_3178_, v___y_3180_);
                v___x_3182_ = leanh::lean_unsigned_to_nat(0);
                v___x_3183_ = 0;
                v___x_3184_ = 1;
                v___x_3185_ =
                    lean_level_mk_data(v___x_3181_, v___x_3182_, v___x_3183_, v___x_3184_);
                v___x_3186_ = leanh::lean_alloc_ctor(4, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_3186_, 0, v_a_3177_);
                leanh::lean_ctor_set_uint64(
                    v___x_3186_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3185_,
                );
                return v___x_3186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_mvar___override(
    mut v_a_3189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3190_: u64 = 0;
    let mut v___x_3191_: u64 = 0;
    let mut v___x_3192_: u64 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: u64 = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = 2237u64;
    v___x_3191_ = l_Lean_instHashableLevelMVarId_hash(v_a_3189_);
    v___x_3192_ = lean_uint64_mix_hash(v___x_3190_, v___x_3191_);
    v___x_3193_ = leanh::lean_unsigned_to_nat(0);
    v___x_3194_ = 1;
    v___x_3195_ = 0;
    v___x_3196_ = lean_level_mk_data(v___x_3192_, v___x_3193_, v___x_3194_, v___x_3195_);
    v___x_3197_ = leanh::lean_alloc_ctor(5, 1, (8) as u32);
    leanh::lean_ctor_set(v___x_3197_, 0, v_a_3189_);
    leanh::lean_ctor_set_uint64(
        v___x_3197_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_3196_,
    );
    return v___x_3197_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevel_default() -> *mut leanh::LeanObject {
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3198_ = leanh::lean_box(0);
    return v___x_3198_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevel() -> *mut leanh::LeanObject {
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3199_ = leanh::lean_box(0);
    return v___x_3199_;
}
pub unsafe fn _init_l_Lean_instReprLevel_repr___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = leanh::lean_unsigned_to_nat(2);
    v___x_3204_ = lean_nat_to_int(v___x_3203_);
    return v___x_3204_;
}
pub unsafe fn _init_l_Lean_instReprLevel_repr___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = leanh::lean_unsigned_to_nat(1);
    v___x_3206_ = lean_nat_to_int(v___x_3205_);
    return v___x_3206_;
}
pub unsafe fn l_Lean_instReprLevel_repr(
    mut v_x_3237_: *mut leanh::LeanObject,
    mut v_prec_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: u8 = 0;
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: u8 = 0;
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3237_) {
                0 => {
                    v___x_3246_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3247_ = lean_nat_dec_le(v___x_3246_, v_prec_3238_);
                    if v___x_3247_ == 0 {
                        v___x_3248_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3240_ = v___x_3248_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3249_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3240_ = v___x_3249_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_3250_ = leanh::lean_ctor_get(v_x_3237_, 0);
                    leanh::lean_inc(v_a_3250_);
                    leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3251_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3261_ = lean_nat_dec_le(v___x_3251_, v_prec_3238_);
                    if v___x_3261_ == 0 {
                        v___x_3262_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3253_ = v___x_3262_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3263_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3253_ = v___x_3263_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_a_3264_ = leanh::lean_ctor_get(v_x_3237_, 0);
                    leanh::lean_inc(v_a_3264_);
                    v_a_3265_ = leanh::lean_ctor_get(v_x_3237_, 1);
                    leanh::lean_inc(v_a_3265_);
                    leanh::lean_dec_ref_known(v_x_3237_, 2);
                    v___x_3266_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3280_ = lean_nat_dec_le(v___x_3266_, v_prec_3238_);
                    if v___x_3280_ == 0 {
                        v___x_3281_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3268_ = v___x_3281_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3282_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3268_ = v___x_3282_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_a_3283_ = leanh::lean_ctor_get(v_x_3237_, 0);
                    leanh::lean_inc(v_a_3283_);
                    v_a_3284_ = leanh::lean_ctor_get(v_x_3237_, 1);
                    leanh::lean_inc(v_a_3284_);
                    leanh::lean_dec_ref_known(v_x_3237_, 2);
                    v___x_3285_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3299_ = lean_nat_dec_le(v___x_3285_, v_prec_3238_);
                    if v___x_3299_ == 0 {
                        v___x_3300_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3287_ = v___x_3300_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3301_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3287_ = v___x_3301_;
                        state = 4;
                        continue;
                    }
                }
                4 => {
                    v_a_3302_ = leanh::lean_ctor_get(v_x_3237_, 0);
                    leanh::lean_inc(v_a_3302_);
                    leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3313_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3314_ = lean_nat_dec_le(v___x_3313_, v_prec_3238_);
                    if v___x_3314_ == 0 {
                        v___x_3315_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3304_ = v___x_3315_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3316_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3304_ = v___x_3316_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_a_3317_ = leanh::lean_ctor_get(v_x_3237_, 0);
                    leanh::lean_inc(v_a_3317_);
                    leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3328_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_3329_ = lean_nat_dec_le(v___x_3328_, v_prec_3238_);
                    if v___x_3329_ == 0 {
                        v___x_3330_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3319_ = v___x_3330_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3331_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__3_once),
                            _init_l_Lean_instReprLevel_repr___closed__3,
                        );
                        v___y_3319_ = v___x_3331_;
                        state = 6;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3241_ = l_Lean_instReprLevel_repr___closed__1;
                leanh::lean_inc(v___y_3240_);
                v___x_3242_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3242_, 0, v___y_3240_);
                leanh::lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                v___x_3243_ = 0;
                v___x_3244_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3244_, 0, v___x_3242_);
                leanh::lean_ctor_set_uint8(
                    v___x_3244_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3243_,
                );
                v___x_3245_ = l_Repr_addAppParen(v___x_3244_, v_prec_3238_);
                return v___x_3245_;
            }
            2 => {
                v___x_3254_ = l_Lean_instReprLevel_repr___closed__6;
                v___x_3255_ = l_Lean_instReprLevel_repr(v_a_3250_, v___x_3251_);
                v___x_3256_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3256_, 0, v___x_3254_);
                leanh::lean_ctor_set(v___x_3256_, 1, v___x_3255_);
                leanh::lean_inc(v___y_3253_);
                v___x_3257_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3257_, 0, v___y_3253_);
                leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
                v___x_3258_ = 0;
                v___x_3259_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3259_, 0, v___x_3257_);
                leanh::lean_ctor_set_uint8(
                    v___x_3259_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3258_,
                );
                v___x_3260_ = l_Repr_addAppParen(v___x_3259_, v_prec_3238_);
                return v___x_3260_;
            }
            3 => {
                v___x_3269_ = leanh::lean_box(1);
                v___x_3270_ = l_Lean_instReprLevel_repr___closed__9;
                v___x_3271_ = l_Lean_instReprLevel_repr(v_a_3264_, v___x_3266_);
                v___x_3272_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                leanh::lean_ctor_set(v___x_3272_, 1, v___x_3271_);
                v___x_3273_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3273_, 0, v___x_3272_);
                leanh::lean_ctor_set(v___x_3273_, 1, v___x_3269_);
                v___x_3274_ = l_Lean_instReprLevel_repr(v_a_3265_, v___x_3266_);
                v___x_3275_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3275_, 0, v___x_3273_);
                leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                leanh::lean_inc(v___y_3268_);
                v___x_3276_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3276_, 0, v___y_3268_);
                leanh::lean_ctor_set(v___x_3276_, 1, v___x_3275_);
                v___x_3277_ = 0;
                v___x_3278_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3278_, 0, v___x_3276_);
                leanh::lean_ctor_set_uint8(
                    v___x_3278_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3277_,
                );
                v___x_3279_ = l_Repr_addAppParen(v___x_3278_, v_prec_3238_);
                return v___x_3279_;
            }
            4 => {
                v___x_3288_ = leanh::lean_box(1);
                v___x_3289_ = l_Lean_instReprLevel_repr___closed__12;
                v___x_3290_ = l_Lean_instReprLevel_repr(v_a_3283_, v___x_3285_);
                v___x_3291_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3291_, 0, v___x_3289_);
                leanh::lean_ctor_set(v___x_3291_, 1, v___x_3290_);
                v___x_3292_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3292_, 0, v___x_3291_);
                leanh::lean_ctor_set(v___x_3292_, 1, v___x_3288_);
                v___x_3293_ = l_Lean_instReprLevel_repr(v_a_3284_, v___x_3285_);
                v___x_3294_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3294_, 0, v___x_3292_);
                leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                leanh::lean_inc(v___y_3287_);
                v___x_3295_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3295_, 0, v___y_3287_);
                leanh::lean_ctor_set(v___x_3295_, 1, v___x_3294_);
                v___x_3296_ = 0;
                v___x_3297_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3297_, 0, v___x_3295_);
                leanh::lean_ctor_set_uint8(
                    v___x_3297_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3296_,
                );
                v___x_3298_ = l_Repr_addAppParen(v___x_3297_, v_prec_3238_);
                return v___x_3298_;
            }
            5 => {
                v___x_3305_ = l_Lean_instReprLevel_repr___closed__15;
                v___x_3306_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3307_ = l_Lean_Name_reprPrec(v_a_3302_, v___x_3306_);
                v___x_3308_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3308_, 0, v___x_3305_);
                leanh::lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                leanh::lean_inc(v___y_3304_);
                v___x_3309_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3309_, 0, v___y_3304_);
                leanh::lean_ctor_set(v___x_3309_, 1, v___x_3308_);
                v___x_3310_ = 0;
                v___x_3311_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3311_, 0, v___x_3309_);
                leanh::lean_ctor_set_uint8(
                    v___x_3311_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3310_,
                );
                v___x_3312_ = l_Repr_addAppParen(v___x_3311_, v_prec_3238_);
                return v___x_3312_;
            }
            6 => {
                v___x_3320_ = l_Lean_instReprLevel_repr___closed__18;
                v___x_3321_ = leanh::lean_unsigned_to_nat(1024);
                v___x_3322_ = l_Lean_Name_reprPrec(v_a_3317_, v___x_3321_);
                v___x_3323_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3323_, 0, v___x_3320_);
                leanh::lean_ctor_set(v___x_3323_, 1, v___x_3322_);
                leanh::lean_inc(v___y_3319_);
                v___x_3324_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3324_, 0, v___y_3319_);
                leanh::lean_ctor_set(v___x_3324_, 1, v___x_3323_);
                v___x_3325_ = 0;
                v___x_3326_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_3326_, 0, v___x_3324_);
                leanh::lean_ctor_set_uint8(
                    v___x_3326_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_3325_,
                );
                v___x_3327_ = l_Repr_addAppParen(v___x_3326_, v_prec_3238_);
                return v___x_3327_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprLevel_repr___boxed(
    mut v_x_3332_: *mut leanh::LeanObject,
    mut v_prec_3333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_instReprLevel_repr(v_x_3332_, v_prec_3333_);
    leanh::lean_dec(v_prec_3333_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_Level_hash(mut v_u_3337_: *mut leanh::LeanObject) -> u64 {
    let mut v___x_3338_: u64 = 0;
    let mut v___x_3339_: u64 = 0;
    v___x_3338_ = l_Lean_Level_data___override(v_u_3337_);
    v___x_3339_ = l_Lean_Level_Data_hash(v___x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Level_hash___boxed(
    mut v_u_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3341_: u64 = 0;
    let mut v_r_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ = l_Lean_Level_hash(v_u_3340_);
    leanh::lean_dec(v_u_3340_);
    v_r_3342_ = leanh::lean_box_uint64(v_res_3341_);
    return v_r_3342_;
}
pub unsafe fn l_Lean_Level_depth(
    mut v_u_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3346_: u64 = 0;
    let mut v___x_3347_: u32 = 0;
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Lean_Level_data___override(v_u_3345_);
    v___x_3347_ = l_Lean_Level_Data_depth(v___x_3346_);
    v___x_3348_ = lean_uint32_to_nat(v___x_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Lean_Level_depth___boxed(
    mut v_u_3349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Lean_Level_depth(v_u_3349_);
    leanh::lean_dec(v_u_3349_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_Level_hasMVar(mut v_u_3351_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3352_: u64 = 0;
    let mut v___x_3353_: u8 = 0;
    v___x_3352_ = l_Lean_Level_data___override(v_u_3351_);
    v___x_3353_ = l_Lean_Level_Data_hasMVar(v___x_3352_);
    return v___x_3353_;
}
pub unsafe fn l_Lean_Level_hasMVar___boxed(
    mut v_u_3354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3355_: u8 = 0;
    let mut v_r_3356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_Level_hasMVar(v_u_3354_);
    leanh::lean_dec(v_u_3354_);
    v_r_3356_ = leanh::lean_box((v_res_3355_) as usize);
    return v_r_3356_;
}
pub unsafe fn l_Lean_Level_hasParam(mut v_u_3357_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3358_: u64 = 0;
    let mut v___x_3359_: u8 = 0;
    v___x_3358_ = l_Lean_Level_data___override(v_u_3357_);
    v___x_3359_ = l_Lean_Level_Data_hasParam(v___x_3358_);
    return v___x_3359_;
}
pub unsafe fn l_Lean_Level_hasParam___boxed(
    mut v_u_3360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3361_: u8 = 0;
    let mut v_r_3362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3361_ = l_Lean_Level_hasParam(v_u_3360_);
    leanh::lean_dec(v_u_3360_);
    v_r_3362_ = leanh::lean_box((v_res_3361_) as usize);
    return v_r_3362_;
}
pub unsafe fn lean_level_hash(mut v_u_3363_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_3364_: u64 = 0;
    let mut v___x_3365_: u32 = 0;
    v___x_3364_ = l_Lean_Level_hash(v_u_3363_);
    leanh::lean_dec(v_u_3363_);
    v___x_3365_ = lean_uint64_to_uint32(v___x_3364_);
    return v___x_3365_;
}
pub unsafe fn l_Lean_Level_hashEx___boxed(
    mut v_u_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3367_: u32 = 0;
    let mut v_r_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3367_ = lean_level_hash(v_u_3366_);
    v_r_3368_ = leanh::lean_box_uint32(v_res_3367_);
    return v_r_3368_;
}
pub unsafe fn lean_level_has_mvar(mut v_u_3369_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3370_: u8 = 0;
    v___x_3370_ = l_Lean_Level_hasMVar(v_u_3369_);
    leanh::lean_dec(v_u_3369_);
    return v___x_3370_;
}
pub unsafe fn l_Lean_Level_hasMVarEx___boxed(
    mut v_u_3371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3372_: u8 = 0;
    let mut v_r_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ = lean_level_has_mvar(v_u_3371_);
    v_r_3373_ = leanh::lean_box((v_res_3372_) as usize);
    return v_r_3373_;
}
pub unsafe fn lean_level_has_param(mut v_u_3374_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3375_: u8 = 0;
    v___x_3375_ = l_Lean_Level_hasParam(v_u_3374_);
    leanh::lean_dec(v_u_3374_);
    return v___x_3375_;
}
pub unsafe fn l_Lean_Level_hasParamEx___boxed(
    mut v_u_3376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3377_: u8 = 0;
    let mut v_r_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3377_ = lean_level_has_param(v_u_3376_);
    v_r_3378_ = leanh::lean_box((v_res_3377_) as usize);
    return v_r_3378_;
}
pub unsafe fn lean_level_depth(mut v_u_3379_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_3380_: u64 = 0;
    let mut v___x_3381_: u32 = 0;
    v___x_3380_ = l_Lean_Level_data___override(v_u_3379_);
    leanh::lean_dec(v_u_3379_);
    v___x_3381_ = l_Lean_Level_Data_depth(v___x_3380_);
    return v___x_3381_;
}
pub unsafe fn l_Lean_Level_depthEx___boxed(
    mut v_u_3382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3383_: u32 = 0;
    let mut v_r_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3383_ = lean_level_depth(v_u_3382_);
    v_r_3384_ = leanh::lean_box_uint32(v_res_3383_);
    return v_r_3384_;
}
pub unsafe fn _init_l_Lean_levelZero() -> *mut leanh::LeanObject {
    let mut v___x_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3385_ = leanh::lean_box(0);
    return v___x_3385_;
}
pub unsafe fn l_Lean_mkLevelMVar(
    mut v_mvarId_3386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ = l_Lean_Level_mvar___override(v_mvarId_3386_);
    return v___x_3387_;
}
pub unsafe fn l_Lean_mkLevelParam(
    mut v_name_3388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Lean_Level_param___override(v_name_3388_);
    return v___x_3389_;
}
pub unsafe fn l_Lean_mkLevelSucc(
    mut v_u_3390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_Level_succ___override(v_u_3390_);
    return v___x_3391_;
}
pub unsafe fn l_Lean_mkLevelMax(
    mut v_u_3392_: *mut leanh::LeanObject,
    mut v_v_3393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Lean_Level_max___override(v_u_3392_, v_v_3393_);
    return v___x_3394_;
}
pub unsafe fn l_Lean_mkLevelIMax(
    mut v_u_3395_: *mut leanh::LeanObject,
    mut v_v_3396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = l_Lean_Level_imax___override(v_u_3395_, v_v_3396_);
    return v___x_3397_;
}
pub unsafe fn _init_l_Lean_Level_one___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = leanh::lean_box(0);
    v___x_3399_ = l_Lean_Level_succ___override(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_Level_one() -> *mut leanh::LeanObject {
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0_once),
        _init_l_Lean_Level_one___closed__0,
    );
    return v___x_3400_;
}
pub unsafe fn _init_l_Lean_levelOne() -> *mut leanh::LeanObject {
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0_once),
        _init_l_Lean_Level_one___closed__0,
    );
    return v___x_3401_;
}
pub unsafe fn lean_level_mk_zero(
    mut v_x_3402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = leanh::lean_box(0);
    return v___x_3403_;
}
pub unsafe fn lean_level_mk_succ(
    mut v_u_3404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = l_Lean_Level_succ___override(v_u_3404_);
    return v___x_3405_;
}
pub unsafe fn lean_level_mk_mvar(
    mut v_mvarId_3406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Level_mvar___override(v_mvarId_3406_);
    return v___x_3407_;
}
pub unsafe fn lean_level_mk_param(
    mut v_name_3408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_Level_param___override(v_name_3408_);
    return v___x_3409_;
}
pub unsafe fn lean_level_mk_max(
    mut v_u_3410_: *mut leanh::LeanObject,
    mut v_v_3411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3412_ = l_Lean_Level_max___override(v_u_3410_, v_v_3411_);
    return v___x_3412_;
}
pub unsafe fn lean_level_mk_imax(
    mut v_u_3413_: *mut leanh::LeanObject,
    mut v_v_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_Level_imax___override(v_u_3413_, v_v_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Lean_Level_isZero(mut v_x_3416_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3416_) == 0 {
        let mut v___x_3417_: u8 = 0;
        v___x_3417_ = 1;
        return v___x_3417_;
    } else {
        let mut v___x_3418_: u8 = 0;
        v___x_3418_ = 0;
        return v___x_3418_;
    }
}
pub unsafe fn l_Lean_Level_isZero___boxed(
    mut v_x_3419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3420_: u8 = 0;
    let mut v_r_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l_Lean_Level_isZero(v_x_3419_);
    leanh::lean_dec(v_x_3419_);
    v_r_3421_ = leanh::lean_box((v_res_3420_) as usize);
    return v_r_3421_;
}
pub unsafe fn l_Lean_Level_isSucc(mut v_x_3422_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3422_) == 1 {
        let mut v___x_3423_: u8 = 0;
        v___x_3423_ = 1;
        return v___x_3423_;
    } else {
        let mut v___x_3424_: u8 = 0;
        v___x_3424_ = 0;
        return v___x_3424_;
    }
}
pub unsafe fn l_Lean_Level_isSucc___boxed(
    mut v_x_3425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3426_: u8 = 0;
    let mut v_r_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Lean_Level_isSucc(v_x_3425_);
    leanh::lean_dec(v_x_3425_);
    v_r_3427_ = leanh::lean_box((v_res_3426_) as usize);
    return v_r_3427_;
}
pub unsafe fn l_Lean_Level_isMax(mut v_x_3428_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3428_) == 2 {
        let mut v___x_3429_: u8 = 0;
        v___x_3429_ = 1;
        return v___x_3429_;
    } else {
        let mut v___x_3430_: u8 = 0;
        v___x_3430_ = 0;
        return v___x_3430_;
    }
}
pub unsafe fn l_Lean_Level_isMax___boxed(
    mut v_x_3431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3432_: u8 = 0;
    let mut v_r_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Level_isMax(v_x_3431_);
    leanh::lean_dec(v_x_3431_);
    v_r_3433_ = leanh::lean_box((v_res_3432_) as usize);
    return v_r_3433_;
}
pub unsafe fn l_Lean_Level_isIMax(mut v_x_3434_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3434_) == 3 {
        let mut v___x_3435_: u8 = 0;
        v___x_3435_ = 1;
        return v___x_3435_;
    } else {
        let mut v___x_3436_: u8 = 0;
        v___x_3436_ = 0;
        return v___x_3436_;
    }
}
pub unsafe fn l_Lean_Level_isIMax___boxed(
    mut v_x_3437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3438_: u8 = 0;
    let mut v_r_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Lean_Level_isIMax(v_x_3437_);
    leanh::lean_dec(v_x_3437_);
    v_r_3439_ = leanh::lean_box((v_res_3438_) as usize);
    return v_r_3439_;
}
pub unsafe fn l_Lean_Level_isMaxIMax(mut v_x_3440_: *mut leanh::LeanObject) -> u8 {
    match leanh::lean_obj_tag(v_x_3440_) {
        2 => {
            let mut v___x_3441_: u8 = 0;
            v___x_3441_ = 1;
            return v___x_3441_;
        }
        3 => {
            let mut v___x_3442_: u8 = 0;
            v___x_3442_ = 1;
            return v___x_3442_;
        }
        _ => {
            let mut v___x_3443_: u8 = 0;
            v___x_3443_ = 0;
            return v___x_3443_;
        }
    }
}
pub unsafe fn l_Lean_Level_isMaxIMax___boxed(
    mut v_x_3444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3445_: u8 = 0;
    let mut v_r_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Lean_Level_isMaxIMax(v_x_3444_);
    leanh::lean_dec(v_x_3444_);
    v_r_3446_ = leanh::lean_box((v_res_3445_) as usize);
    return v_r_3446_;
}
pub unsafe fn l_Lean_Level_isParam(mut v_x_3447_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3447_) == 4 {
        let mut v___x_3448_: u8 = 0;
        v___x_3448_ = 1;
        return v___x_3448_;
    } else {
        let mut v___x_3449_: u8 = 0;
        v___x_3449_ = 0;
        return v___x_3449_;
    }
}
pub unsafe fn l_Lean_Level_isParam___boxed(
    mut v_x_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3451_: u8 = 0;
    let mut v_r_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3451_ = l_Lean_Level_isParam(v_x_3450_);
    leanh::lean_dec(v_x_3450_);
    v_r_3452_ = leanh::lean_box((v_res_3451_) as usize);
    return v_r_3452_;
}
pub unsafe fn l_Lean_Level_isMVar(mut v_x_3453_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_3453_) == 5 {
        let mut v___x_3454_: u8 = 0;
        v___x_3454_ = 1;
        return v___x_3454_;
    } else {
        let mut v___x_3455_: u8 = 0;
        v___x_3455_ = 0;
        return v___x_3455_;
    }
}
pub unsafe fn l_Lean_Level_isMVar___boxed(
    mut v_x_3456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3457_: u8 = 0;
    let mut v_r_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3457_ = l_Lean_Level_isMVar(v_x_3456_);
    leanh::lean_dec(v_x_3456_);
    v_r_3458_ = leanh::lean_box((v_res_3457_) as usize);
    return v_r_3458_;
}
pub unsafe fn l_panic___at___00Lean_Level_mvarId_x21_spec__0(
    mut v_msg_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3460_ = leanh::lean_box(0);
    v___x_3461_ = lean_panic_fn_borrowed(v___x_3460_, v_msg_3459_);
    return v___x_3461_;
}
pub unsafe fn _init_l_Lean_Level_mvarId_x21___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Lean_Level_mvarId_x21___closed__2;
    v___x_3466_ = leanh::lean_unsigned_to_nat(19);
    v___x_3467_ = leanh::lean_unsigned_to_nat(195);
    v___x_3468_ = l_Lean_Level_mvarId_x21___closed__1;
    v___x_3469_ = l_Lean_Level_mvarId_x21___closed__0;
    v___x_3470_ = l_mkPanicMessageWithDecl(
        v___x_3469_,
        v___x_3468_,
        v___x_3467_,
        v___x_3466_,
        v___x_3465_,
    );
    return v___x_3470_;
}
pub unsafe fn l_Lean_Level_mvarId_x21(
    mut v_x_3471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_3471_) == 5 {
        let mut v_a_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_3472_ = leanh::lean_ctor_get(v_x_3471_, 0);
        leanh::lean_inc(v_a_3472_);
        return v_a_3472_;
    } else {
        let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3473_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Level_mvarId_x21___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Level_mvarId_x21___closed__3_once),
            _init_l_Lean_Level_mvarId_x21___closed__3,
        );
        v___x_3474_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_3473_);
        return v___x_3474_;
    }
}
pub unsafe fn l_Lean_Level_mvarId_x21___boxed(
    mut v_x_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_Level_mvarId_x21(v_x_3475_);
    leanh::lean_dec(v_x_3475_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_Level_isNeverZero(mut v_x_3477_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: u8 = 0;
    let mut v_a_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u8 = 0;
    let mut v_a_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3477_) {
                0 => {
                    v___x_3478_ = 0;
                    return v___x_3478_;
                }
                1 => {
                    v___x_3479_ = 1;
                    return v___x_3479_;
                }
                2 => {
                    v_a_3480_ = leanh::lean_ctor_get(v_x_3477_, 0);
                    v_a_3481_ = leanh::lean_ctor_get(v_x_3477_, 1);
                    v___x_3482_ = l_Lean_Level_isNeverZero(v_a_3480_);
                    if v___x_3482_ == 0 {
                        v_x_3477_ = v_a_3481_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3482_;
                    }
                }
                3 => {
                    v_a_3484_ = leanh::lean_ctor_get(v_x_3477_, 1);
                    v_x_3477_ = v_a_3484_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_3486_ = 0;
                    return v___x_3486_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_isNeverZero___boxed(
    mut v_x_3487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3488_: u8 = 0;
    let mut v_r_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Lean_Level_isNeverZero(v_x_3487_);
    leanh::lean_dec(v_x_3487_);
    v_r_3489_ = leanh::lean_box((v_res_3488_) as usize);
    return v_r_3489_;
}
pub unsafe fn l_Lean_Level_isAlwaysZero(mut v_x_3490_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3491_: u8 = 0;
    let mut v_a_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: u8 = 0;
    let mut v_a_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3490_) {
                0 => {
                    v___x_3491_ = 1;
                    return v___x_3491_;
                }
                2 => {
                    v_a_3492_ = leanh::lean_ctor_get(v_x_3490_, 0);
                    v_a_3493_ = leanh::lean_ctor_get(v_x_3490_, 1);
                    v___x_3494_ = l_Lean_Level_isAlwaysZero(v_a_3492_);
                    if v___x_3494_ == 0 {
                        return v___x_3494_;
                    } else {
                        v_x_3490_ = v_a_3493_;
                        state = 0;
                        continue;
                    }
                }
                3 => {
                    v_a_3496_ = leanh::lean_ctor_get(v_x_3490_, 1);
                    v_x_3490_ = v_a_3496_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_3498_ = 0;
                    return v___x_3498_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_isAlwaysZero___boxed(
    mut v_x_3499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3500_: u8 = 0;
    let mut v_r_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Lean_Level_isAlwaysZero(v_x_3499_);
    leanh::lean_dec(v_x_3499_);
    v_r_3501_ = leanh::lean_box((v_res_3500_) as usize);
    return v_r_3501_;
}
pub unsafe fn l_Lean_Level_ofNat(
    mut v_x_3502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3504_: u8 = 0;
    v_zero_3503_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_3504_ = lean_nat_dec_eq(v_x_3502_, v_zero_3503_);
    if v_isZero_3504_ == 1 {
        let mut v___x_3505_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3505_ = leanh::lean_box(0);
        return v___x_3505_;
    } else {
        let mut v_one_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_3506_ = leanh::lean_unsigned_to_nat(1);
        v_n_3507_ = lean_nat_sub(v_x_3502_, v_one_3506_);
        v___x_3508_ = l_Lean_Level_ofNat(v_n_3507_);
        leanh::lean_dec(v_n_3507_);
        v___x_3509_ = l_Lean_Level_succ___override(v___x_3508_);
        return v___x_3509_;
    }
}
pub unsafe fn l_Lean_Level_ofNat___boxed(
    mut v_x_3510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3511_ = l_Lean_Level_ofNat(v_x_3510_);
    leanh::lean_dec(v_x_3510_);
    return v_res_3511_;
}
pub unsafe fn l_Lean_Level_instOfNat(
    mut v_n_3512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_Lean_Level_ofNat(v_n_3512_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_Level_instOfNat___boxed(
    mut v_n_3514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ = l_Lean_Level_instOfNat(v_n_3514_);
    leanh::lean_dec(v_n_3514_);
    return v_res_3515_;
}
pub unsafe fn l_Lean_Level_addOffsetAux(
    mut v_x_3516_: *mut leanh::LeanObject,
    mut v_x_3517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3519_: u8 = 0;
    let mut v_one_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3518_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_3519_ = lean_nat_dec_eq(v_x_3516_, v_zero_3518_);
                if v_isZero_3519_ == 1 {
                    leanh::lean_dec(v_x_3516_);
                    return v_x_3517_;
                } else {
                    v_one_3520_ = leanh::lean_unsigned_to_nat(1);
                    v_n_3521_ = lean_nat_sub(v_x_3516_, v_one_3520_);
                    leanh::lean_dec(v_x_3516_);
                    v___x_3522_ = l_Lean_Level_succ___override(v_x_3517_);
                    v_x_3516_ = v_n_3521_;
                    v_x_3517_ = v___x_3522_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_addOffset(
    mut v_u_3524_: *mut leanh::LeanObject,
    mut v_n_3525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Level_addOffsetAux(v_n_3525_, v_u_3524_);
    return v___x_3526_;
}
pub unsafe fn l_Lean_Level_isExplicit(mut v_x_3527_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_3528_: u8 = 0;
    let mut v_a_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3527_) {
                0 => {
                    v___x_3528_ = 1;
                    return v___x_3528_;
                }
                1 => {
                    v_a_3529_ = leanh::lean_ctor_get(v_x_3527_, 0);
                    v___x_3530_ = l_Lean_Level_hasMVar(v_a_3529_);
                    if v___x_3530_ == 0 {
                        v___x_3531_ = l_Lean_Level_hasParam(v_a_3529_);
                        if v___x_3531_ == 0 {
                            v_x_3527_ = v_a_3529_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_3530_;
                        }
                    } else {
                        v___x_3533_ = 0;
                        return v___x_3533_;
                    }
                }
                _ => {
                    v___x_3534_ = 0;
                    return v___x_3534_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_isExplicit___boxed(
    mut v_x_3535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3536_: u8 = 0;
    let mut v_r_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3536_ = l_Lean_Level_isExplicit(v_x_3535_);
    leanh::lean_dec(v_x_3535_);
    v_r_3537_ = leanh::lean_box((v_res_3536_) as usize);
    return v_r_3537_;
}
pub unsafe fn l_Lean_Level_getOffsetAux(
    mut v_x_3538_: *mut leanh::LeanObject,
    mut v_x_3539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3538_) == 1 {
                    v_a_3540_ = leanh::lean_ctor_get(v_x_3538_, 0);
                    v___x_3541_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3542_ = lean_nat_add(v_x_3539_, v___x_3541_);
                    leanh::lean_dec(v_x_3539_);
                    v_x_3538_ = v_a_3540_;
                    v_x_3539_ = v___x_3542_;
                    state = 0;
                    continue;
                } else {
                    return v_x_3539_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_getOffsetAux___boxed(
    mut v_x_3544_: *mut leanh::LeanObject,
    mut v_x_3545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Lean_Level_getOffsetAux(v_x_3544_, v_x_3545_);
    leanh::lean_dec(v_x_3544_);
    return v_res_3546_;
}
pub unsafe fn l_Lean_Level_getOffset(
    mut v_lvl_3547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = leanh::lean_unsigned_to_nat(0);
    v___x_3549_ = l_Lean_Level_getOffsetAux(v_lvl_3547_, v___x_3548_);
    return v___x_3549_;
}
pub unsafe fn l_Lean_Level_getOffset___boxed(
    mut v_lvl_3550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l_Lean_Level_getOffset(v_lvl_3550_);
    leanh::lean_dec(v_lvl_3550_);
    return v_res_3551_;
}
pub unsafe fn l_Lean_Level_getLevelOffset(
    mut v_x_3552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3552_) == 1 {
                    v_a_3553_ = leanh::lean_ctor_get(v_x_3552_, 0);
                    v_x_3552_ = v_a_3553_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_x_3552_);
                    return v_x_3552_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_getLevelOffset___boxed(
    mut v_x_3555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Lean_Level_getLevelOffset(v_x_3555_);
    leanh::lean_dec(v_x_3555_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Level_toNat(
    mut v_lvl_3557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Level_getLevelOffset(v_lvl_3557_);
    if leanh::lean_obj_tag(v___x_3558_) == 0 {
        let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3559_ = l_Lean_Level_getOffset(v_lvl_3557_);
        v___x_3560_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3560_, 0, v___x_3559_);
        return v___x_3560_;
    } else {
        let mut v___x_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3558_);
        v___x_3561_ = leanh::lean_box(0);
        return v___x_3561_;
    }
}
pub unsafe fn l_Lean_Level_toNat___boxed(
    mut v_lvl_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3563_ = l_Lean_Level_toNat(v_lvl_3562_);
    leanh::lean_dec(v_lvl_3562_);
    return v_res_3563_;
}
pub unsafe fn l_Lean_Level_beq___boxed(
    mut v_a_3566_: *mut leanh::LeanObject,
    mut v_b_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3568_: u8 = 0;
    let mut v_r_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = lean_level_eq(v_a_3566_, v_b_3567_);
    leanh::lean_dec(v_b_3567_);
    leanh::lean_dec(v_a_3566_);
    v_r_3569_ = leanh::lean_box((v_res_3568_) as usize);
    return v_r_3569_;
}
pub unsafe fn l_Lean_Level_occurs(
    mut v_x_3572_: *mut leanh::LeanObject,
    mut v_x_3573_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_a_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: u8 = 0;
    let mut v_a_3577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: u8 = 0;
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: u8 = 0;
    let mut v_a_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: u8 = 0;
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3573_) {
                1 => {
                    v_a_3574_ = leanh::lean_ctor_get(v_x_3573_, 0);
                    v___x_3575_ = lean_level_eq(v_x_3572_, v_x_3573_);
                    if v___x_3575_ == 0 {
                        v_x_3573_ = v_a_3574_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3575_;
                    }
                }
                2 => {
                    v_a_3577_ = leanh::lean_ctor_get(v_x_3573_, 0);
                    v_a_3578_ = leanh::lean_ctor_get(v_x_3573_, 1);
                    v___x_3582_ = lean_level_eq(v_x_3572_, v_x_3573_);
                    if v___x_3582_ == 0 {
                        v___x_3583_ = l_Lean_Level_occurs(v_x_3572_, v_a_3577_);
                        v___y_3580_ = v___x_3583_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3580_ = v___x_3582_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_a_3584_ = leanh::lean_ctor_get(v_x_3573_, 0);
                    v_a_3585_ = leanh::lean_ctor_get(v_x_3573_, 1);
                    v___x_3589_ = lean_level_eq(v_x_3572_, v_x_3573_);
                    if v___x_3589_ == 0 {
                        v___x_3590_ = l_Lean_Level_occurs(v_x_3572_, v_a_3584_);
                        v___y_3587_ = v___x_3590_;
                        state = 2;
                        continue;
                    } else {
                        v___y_3587_ = v___x_3589_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_3591_ = lean_level_eq(v_x_3572_, v_x_3573_);
                    return v___x_3591_;
                }
            },
            1 => {
                if v___y_3580_ == 0 {
                    v_x_3573_ = v_a_3578_;
                    state = 0;
                    continue;
                } else {
                    return v___y_3580_;
                }
            }
            2 => {
                if v___y_3587_ == 0 {
                    v_x_3573_ = v_a_3585_;
                    state = 0;
                    continue;
                } else {
                    return v___y_3587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_occurs___boxed(
    mut v_x_3592_: *mut leanh::LeanObject,
    mut v_x_3593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3594_: u8 = 0;
    let mut v_r_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_Lean_Level_occurs(v_x_3592_, v_x_3593_);
    leanh::lean_dec(v_x_3593_);
    leanh::lean_dec(v_x_3592_);
    v_r_3595_ = leanh::lean_box((v_res_3594_) as usize);
    return v_r_3595_;
}
pub unsafe fn l_Lean_Level_ctorToNat(
    mut v_x_3596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3596_) {
        0 => {
            let mut v___x_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3597_ = leanh::lean_unsigned_to_nat(0);
            return v___x_3597_;
        }
        1 => {
            let mut v___x_3598_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3598_ = leanh::lean_unsigned_to_nat(3);
            return v___x_3598_;
        }
        2 => {
            let mut v___x_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3599_ = leanh::lean_unsigned_to_nat(4);
            return v___x_3599_;
        }
        3 => {
            let mut v___x_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3600_ = leanh::lean_unsigned_to_nat(5);
            return v___x_3600_;
        }
        4 => {
            let mut v___x_3601_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3601_ = leanh::lean_unsigned_to_nat(1);
            return v___x_3601_;
        }
        _ => {
            let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3602_ = leanh::lean_unsigned_to_nat(2);
            return v___x_3602_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorToNat___boxed(
    mut v_x_3603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3604_ = l_Lean_Level_ctorToNat(v_x_3603_);
    leanh::lean_dec(v_x_3603_);
    return v_res_3604_;
}
pub unsafe fn l_Lean_Level_normLtAux(
    mut v_x_3605_: *mut leanh::LeanObject,
    mut v_x_3606_: *mut leanh::LeanObject,
    mut v_x_3607_: *mut leanh::LeanObject,
    mut v_x_3608_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_l_u2081_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2081_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_3620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: u8 = 0;
    let mut v___x_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: u8 = 0;
    let mut v_a_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: u8 = 0;
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v_a_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v_a_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v_a_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: u8 = 0;
    let mut v_a_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3605_) {
                1 => {
                    v_a_3627_ = leanh::lean_ctor_get(v_x_3605_, 0);
                    v___x_3628_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3629_ = lean_nat_add(v_x_3606_, v___x_3628_);
                    leanh::lean_dec(v_x_3606_);
                    v_x_3605_ = v_a_3627_;
                    v_x_3606_ = v___x_3629_;
                    state = 0;
                    continue;
                }
                2 => match leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3631_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3631_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v_a_3632_ = leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3633_ = leanh::lean_ctor_get(v_x_3605_, 1);
                        v_a_3634_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_a_3635_ = leanh::lean_ctor_get(v_x_3607_, 1);
                        v___x_3639_ = lean_level_eq(v_x_3605_, v_x_3607_);
                        if v___x_3639_ == 0 {
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            v___x_3640_ = lean_level_eq(v_a_3632_, v_a_3634_);
                            if v___x_3640_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_3639_ == 0 {
                                    v___x_3641_ = leanh::lean_unsigned_to_nat(0);
                                    v_x_3605_ = v_a_3633_;
                                    v_x_3606_ = v___x_3641_;
                                    v_x_3607_ = v_a_3635_;
                                    v_x_3608_ = v___x_3641_;
                                    state = 0;
                                    continue;
                                } else {
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3643_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            return v___x_3643_;
                        }
                    }
                    _ => {
                        v_l_u2081_3618_ = v_x_3605_;
                        v_k_u2081_3619_ = v_x_3606_;
                        v_l_u2082_3620_ = v_x_3607_;
                        v_k_u2082_3621_ = v_x_3608_;
                        state = 2;
                        continue;
                    }
                },
                3 => match leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3644_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3644_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_a_3645_ = leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3646_ = leanh::lean_ctor_get(v_x_3605_, 1);
                        v_a_3647_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_a_3648_ = leanh::lean_ctor_get(v_x_3607_, 1);
                        v___x_3652_ = lean_level_eq(v_x_3605_, v_x_3607_);
                        if v___x_3652_ == 0 {
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            v___x_3653_ = lean_level_eq(v_a_3645_, v_a_3647_);
                            if v___x_3653_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                if v___x_3652_ == 0 {
                                    v___x_3654_ = leanh::lean_unsigned_to_nat(0);
                                    v_x_3605_ = v_a_3646_;
                                    v_x_3606_ = v___x_3654_;
                                    v_x_3607_ = v_a_3648_;
                                    v_x_3608_ = v___x_3654_;
                                    state = 0;
                                    continue;
                                } else {
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            v___x_3656_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            return v___x_3656_;
                        }
                    }
                    _ => {
                        v_l_u2081_3618_ = v_x_3605_;
                        v_k_u2081_3619_ = v_x_3606_;
                        v_l_u2082_3620_ = v_x_3607_;
                        v_k_u2082_3621_ = v_x_3608_;
                        state = 2;
                        continue;
                    }
                },
                4 => match leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3657_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3657_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_a_3658_ = leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3659_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v___x_3660_ = lean_name_eq(v_a_3658_, v_a_3659_);
                        if v___x_3660_ == 0 {
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            v___x_3661_ = l_Lean_Name_lt(v_a_3658_, v_a_3659_);
                            return v___x_3661_;
                        } else {
                            v___x_3662_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            return v___x_3662_;
                        }
                    }
                    _ => {
                        v_l_u2081_3618_ = v_x_3605_;
                        v_k_u2081_3619_ = v_x_3606_;
                        v_l_u2082_3620_ = v_x_3607_;
                        v_k_u2082_3621_ = v_x_3608_;
                        state = 2;
                        continue;
                    }
                },
                5 => match leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3663_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3663_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_a_3664_ = leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3665_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v___x_3666_ = lean_name_eq(v_a_3664_, v_a_3665_);
                        if v___x_3666_ == 0 {
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            v___x_3667_ = l_Lean_Name_lt(v_a_3664_, v_a_3665_);
                            return v___x_3667_;
                        } else {
                            v___x_3668_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            leanh::lean_dec(v_x_3608_);
                            leanh::lean_dec(v_x_3606_);
                            return v___x_3668_;
                        }
                    }
                    _ => {
                        v_l_u2081_3618_ = v_x_3605_;
                        v_k_u2081_3619_ = v_x_3606_;
                        v_l_u2082_3620_ = v_x_3607_;
                        v_k_u2082_3621_ = v_x_3608_;
                        state = 2;
                        continue;
                    }
                },
                _ => {
                    if leanh::lean_obj_tag(v_x_3607_) == 1 {
                        v_a_3669_ = leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3669_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    } else {
                        v_l_u2081_3618_ = v_x_3605_;
                        v_k_u2081_3619_ = v_x_3606_;
                        v_l_u2082_3620_ = v_x_3607_;
                        v_k_u2082_3621_ = v_x_3608_;
                        state = 2;
                        continue;
                    }
                }
            },
            1 => {
                v___x_3614_ = leanh::lean_unsigned_to_nat(1);
                v___x_3615_ = lean_nat_add(v_k_u2082_3613_, v___x_3614_);
                leanh::lean_dec(v_k_u2082_3613_);
                v_x_3605_ = v_l_u2081_3610_;
                v_x_3606_ = v_k_u2081_3611_;
                v_x_3607_ = v_l_u2082_3612_;
                v_x_3608_ = v___x_3615_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3622_ = lean_level_eq(v_l_u2081_3618_, v_l_u2082_3620_);
                if v___x_3622_ == 0 {
                    leanh::lean_dec(v_k_u2082_3621_);
                    leanh::lean_dec(v_k_u2081_3619_);
                    v___x_3623_ = l_Lean_Level_ctorToNat(v_l_u2081_3618_);
                    v___x_3624_ = l_Lean_Level_ctorToNat(v_l_u2082_3620_);
                    v___x_3625_ = lean_nat_dec_lt(v___x_3623_, v___x_3624_);
                    leanh::lean_dec(v___x_3624_);
                    leanh::lean_dec(v___x_3623_);
                    return v___x_3625_;
                } else {
                    v___x_3626_ = lean_nat_dec_lt(v_k_u2081_3619_, v_k_u2082_3621_);
                    leanh::lean_dec(v_k_u2082_3621_);
                    leanh::lean_dec(v_k_u2081_3619_);
                    return v___x_3626_;
                }
            }
            3 => {
                v___x_3637_ = leanh::lean_unsigned_to_nat(0);
                v_x_3605_ = v_a_3632_;
                v_x_3606_ = v___x_3637_;
                v_x_3607_ = v_a_3634_;
                v_x_3608_ = v___x_3637_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3650_ = leanh::lean_unsigned_to_nat(0);
                v_x_3605_ = v_a_3645_;
                v_x_3606_ = v___x_3650_;
                v_x_3607_ = v_a_3647_;
                v_x_3608_ = v___x_3650_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_normLtAux___boxed(
    mut v_x_3670_: *mut leanh::LeanObject,
    mut v_x_3671_: *mut leanh::LeanObject,
    mut v_x_3672_: *mut leanh::LeanObject,
    mut v_x_3673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3674_: u8 = 0;
    let mut v_r_3675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Lean_Level_normLtAux(v_x_3670_, v_x_3671_, v_x_3672_, v_x_3673_);
    leanh::lean_dec(v_x_3672_);
    leanh::lean_dec(v_x_3670_);
    v_r_3675_ = leanh::lean_box((v_res_3674_) as usize);
    return v_r_3675_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(
    mut v_x_3676_: *mut leanh::LeanObject,
    mut v_x_3677_: *mut leanh::LeanObject,
    mut v_x_3678_: *mut leanh::LeanObject,
    mut v_x_3679_: *mut leanh::LeanObject,
    mut v_h__1_3680_: *mut leanh::LeanObject,
    mut v_h__2_3681_: *mut leanh::LeanObject,
    mut v_h__3_3682_: *mut leanh::LeanObject,
    mut v_h__4_3683_: *mut leanh::LeanObject,
    mut v_h__5_3684_: *mut leanh::LeanObject,
    mut v_h__6_3685_: *mut leanh::LeanObject,
    mut v_h__7_3686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3676_) {
        1 => {
            let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_3686_);
            leanh::lean_dec(v_h__6_3685_);
            leanh::lean_dec(v_h__5_3684_);
            leanh::lean_dec(v_h__4_3683_);
            leanh::lean_dec(v_h__3_3682_);
            leanh::lean_dec(v_h__2_3681_);
            v_a_3687_ = leanh::lean_ctor_get(v_x_3676_, 0);
            leanh::lean_inc(v_a_3687_);
            leanh::lean_dec_ref_known(v_x_3676_, 1);
            v___x_3688_ = leanh::lean_apply_4(
                v_h__1_3680_,
                v_a_3687_,
                v_x_3677_,
                v_x_3678_,
                v_x_3679_,
            );
            return v___x_3688_;
        }
        2 => {
            leanh::lean_dec(v_h__6_3685_);
            leanh::lean_dec(v_h__5_3684_);
            leanh::lean_dec(v_h__4_3683_);
            leanh::lean_dec(v_h__1_3680_);
            match leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__3_3682_);
                    v_a_3689_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3689_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3690_ = leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3689_,
                        v_x_3679_,
                        leanh::lean_box(0),
                    );
                    return v___x_3690_;
                }
                2 => {
                    let mut v_a_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__2_3681_);
                    v_a_3691_ = leanh::lean_ctor_get(v_x_3676_, 0);
                    leanh::lean_inc(v_a_3691_);
                    v_a_3692_ = leanh::lean_ctor_get(v_x_3676_, 1);
                    leanh::lean_inc(v_a_3692_);
                    leanh::lean_dec_ref_known(v_x_3676_, 2);
                    v_a_3693_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3693_);
                    v_a_3694_ = leanh::lean_ctor_get(v_x_3678_, 1);
                    leanh::lean_inc(v_a_3694_);
                    leanh::lean_dec_ref_known(v_x_3678_, 2);
                    v___x_3695_ = leanh::lean_apply_6(
                        v_h__3_3682_,
                        v_a_3691_,
                        v_a_3692_,
                        v_x_3677_,
                        v_a_3693_,
                        v_a_3694_,
                        v_x_3679_,
                    );
                    return v___x_3695_;
                }
                _ => {
                    let mut v___x_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__3_3682_);
                    leanh::lean_dec(v_h__2_3681_);
                    v___x_3696_ = leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3696_;
                }
            }
        }
        3 => {
            leanh::lean_dec(v_h__6_3685_);
            leanh::lean_dec(v_h__5_3684_);
            leanh::lean_dec(v_h__3_3682_);
            leanh::lean_dec(v_h__1_3680_);
            match leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3697_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__4_3683_);
                    v_a_3697_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3697_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3698_ = leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3697_,
                        v_x_3679_,
                        leanh::lean_box(0),
                    );
                    return v___x_3698_;
                }
                3 => {
                    let mut v_a_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3703_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__2_3681_);
                    v_a_3699_ = leanh::lean_ctor_get(v_x_3676_, 0);
                    leanh::lean_inc(v_a_3699_);
                    v_a_3700_ = leanh::lean_ctor_get(v_x_3676_, 1);
                    leanh::lean_inc(v_a_3700_);
                    leanh::lean_dec_ref_known(v_x_3676_, 2);
                    v_a_3701_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3701_);
                    v_a_3702_ = leanh::lean_ctor_get(v_x_3678_, 1);
                    leanh::lean_inc(v_a_3702_);
                    leanh::lean_dec_ref_known(v_x_3678_, 2);
                    v___x_3703_ = leanh::lean_apply_6(
                        v_h__4_3683_,
                        v_a_3699_,
                        v_a_3700_,
                        v_x_3677_,
                        v_a_3701_,
                        v_a_3702_,
                        v_x_3679_,
                    );
                    return v___x_3703_;
                }
                _ => {
                    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__4_3683_);
                    leanh::lean_dec(v_h__2_3681_);
                    v___x_3704_ = leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3704_;
                }
            }
        }
        4 => {
            leanh::lean_dec(v_h__6_3685_);
            leanh::lean_dec(v_h__4_3683_);
            leanh::lean_dec(v_h__3_3682_);
            leanh::lean_dec(v_h__1_3680_);
            match leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3706_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__5_3684_);
                    v_a_3705_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3705_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3706_ = leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3705_,
                        v_x_3679_,
                        leanh::lean_box(0),
                    );
                    return v___x_3706_;
                }
                4 => {
                    let mut v_a_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__2_3681_);
                    v_a_3707_ = leanh::lean_ctor_get(v_x_3676_, 0);
                    leanh::lean_inc(v_a_3707_);
                    leanh::lean_dec_ref_known(v_x_3676_, 1);
                    v_a_3708_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3708_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3709_ = leanh::lean_apply_4(
                        v_h__5_3684_,
                        v_a_3707_,
                        v_x_3677_,
                        v_a_3708_,
                        v_x_3679_,
                    );
                    return v___x_3709_;
                }
                _ => {
                    let mut v___x_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__5_3684_);
                    leanh::lean_dec(v_h__2_3681_);
                    v___x_3710_ = leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3710_;
                }
            }
        }
        5 => {
            leanh::lean_dec(v_h__5_3684_);
            leanh::lean_dec(v_h__4_3683_);
            leanh::lean_dec(v_h__3_3682_);
            leanh::lean_dec(v_h__1_3680_);
            match leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__6_3685_);
                    v_a_3711_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3711_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3712_ = leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3711_,
                        v_x_3679_,
                        leanh::lean_box(0),
                    );
                    return v___x_3712_;
                }
                5 => {
                    let mut v_a_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3686_);
                    leanh::lean_dec(v_h__2_3681_);
                    v_a_3713_ = leanh::lean_ctor_get(v_x_3676_, 0);
                    leanh::lean_inc(v_a_3713_);
                    leanh::lean_dec_ref_known(v_x_3676_, 1);
                    v_a_3714_ = leanh::lean_ctor_get(v_x_3678_, 0);
                    leanh::lean_inc(v_a_3714_);
                    leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3715_ = leanh::lean_apply_4(
                        v_h__6_3685_,
                        v_a_3713_,
                        v_x_3677_,
                        v_a_3714_,
                        v_x_3679_,
                    );
                    return v___x_3715_;
                }
                _ => {
                    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_3685_);
                    leanh::lean_dec(v_h__2_3681_);
                    v___x_3716_ = leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3716_;
                }
            }
        }
        _ => {
            leanh::lean_dec(v_h__6_3685_);
            leanh::lean_dec(v_h__5_3684_);
            leanh::lean_dec(v_h__4_3683_);
            leanh::lean_dec(v_h__3_3682_);
            leanh::lean_dec(v_h__1_3680_);
            if leanh::lean_obj_tag(v_x_3678_) == 1 {
                let mut v_a_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__7_3686_);
                v_a_3717_ = leanh::lean_ctor_get(v_x_3678_, 0);
                leanh::lean_inc(v_a_3717_);
                leanh::lean_dec_ref_known(v_x_3678_, 1);
                v___x_3718_ = leanh::lean_apply_5(
                    v_h__2_3681_,
                    v_x_3676_,
                    v_x_3677_,
                    v_a_3717_,
                    v_x_3679_,
                    leanh::lean_box(0),
                );
                return v___x_3718_;
            } else {
                let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_3681_);
                v___x_3719_ = leanh::lean_apply_10(
                    v_h__7_3686_,
                    v_x_3676_,
                    v_x_3677_,
                    v_x_3678_,
                    v_x_3679_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_3719_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(
    mut v_motive_3720_: *mut leanh::LeanObject,
    mut v_x_3721_: *mut leanh::LeanObject,
    mut v_x_3722_: *mut leanh::LeanObject,
    mut v_x_3723_: *mut leanh::LeanObject,
    mut v_x_3724_: *mut leanh::LeanObject,
    mut v_h__1_3725_: *mut leanh::LeanObject,
    mut v_h__2_3726_: *mut leanh::LeanObject,
    mut v_h__3_3727_: *mut leanh::LeanObject,
    mut v_h__4_3728_: *mut leanh::LeanObject,
    mut v_h__5_3729_: *mut leanh::LeanObject,
    mut v_h__6_3730_: *mut leanh::LeanObject,
    mut v_h__7_3731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_3721_) {
        1 => {
            let mut v_a_3732_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__7_3731_);
            leanh::lean_dec(v_h__6_3730_);
            leanh::lean_dec(v_h__5_3729_);
            leanh::lean_dec(v_h__4_3728_);
            leanh::lean_dec(v_h__3_3727_);
            leanh::lean_dec(v_h__2_3726_);
            v_a_3732_ = leanh::lean_ctor_get(v_x_3721_, 0);
            leanh::lean_inc(v_a_3732_);
            leanh::lean_dec_ref_known(v_x_3721_, 1);
            v___x_3733_ = leanh::lean_apply_4(
                v_h__1_3725_,
                v_a_3732_,
                v_x_3722_,
                v_x_3723_,
                v_x_3724_,
            );
            return v___x_3733_;
        }
        2 => {
            leanh::lean_dec(v_h__6_3730_);
            leanh::lean_dec(v_h__5_3729_);
            leanh::lean_dec(v_h__4_3728_);
            leanh::lean_dec(v_h__1_3725_);
            match leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__3_3727_);
                    v_a_3734_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3734_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3735_ = leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3734_,
                        v_x_3724_,
                        leanh::lean_box(0),
                    );
                    return v___x_3735_;
                }
                2 => {
                    let mut v_a_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__2_3726_);
                    v_a_3736_ = leanh::lean_ctor_get(v_x_3721_, 0);
                    leanh::lean_inc(v_a_3736_);
                    v_a_3737_ = leanh::lean_ctor_get(v_x_3721_, 1);
                    leanh::lean_inc(v_a_3737_);
                    leanh::lean_dec_ref_known(v_x_3721_, 2);
                    v_a_3738_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3738_);
                    v_a_3739_ = leanh::lean_ctor_get(v_x_3723_, 1);
                    leanh::lean_inc(v_a_3739_);
                    leanh::lean_dec_ref_known(v_x_3723_, 2);
                    v___x_3740_ = leanh::lean_apply_6(
                        v_h__3_3727_,
                        v_a_3736_,
                        v_a_3737_,
                        v_x_3722_,
                        v_a_3738_,
                        v_a_3739_,
                        v_x_3724_,
                    );
                    return v___x_3740_;
                }
                _ => {
                    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__3_3727_);
                    leanh::lean_dec(v_h__2_3726_);
                    v___x_3741_ = leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3741_;
                }
            }
        }
        3 => {
            leanh::lean_dec(v_h__6_3730_);
            leanh::lean_dec(v_h__5_3729_);
            leanh::lean_dec(v_h__3_3727_);
            leanh::lean_dec(v_h__1_3725_);
            match leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__4_3728_);
                    v_a_3742_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3742_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3743_ = leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3742_,
                        v_x_3724_,
                        leanh::lean_box(0),
                    );
                    return v___x_3743_;
                }
                3 => {
                    let mut v_a_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__2_3726_);
                    v_a_3744_ = leanh::lean_ctor_get(v_x_3721_, 0);
                    leanh::lean_inc(v_a_3744_);
                    v_a_3745_ = leanh::lean_ctor_get(v_x_3721_, 1);
                    leanh::lean_inc(v_a_3745_);
                    leanh::lean_dec_ref_known(v_x_3721_, 2);
                    v_a_3746_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3746_);
                    v_a_3747_ = leanh::lean_ctor_get(v_x_3723_, 1);
                    leanh::lean_inc(v_a_3747_);
                    leanh::lean_dec_ref_known(v_x_3723_, 2);
                    v___x_3748_ = leanh::lean_apply_6(
                        v_h__4_3728_,
                        v_a_3744_,
                        v_a_3745_,
                        v_x_3722_,
                        v_a_3746_,
                        v_a_3747_,
                        v_x_3724_,
                    );
                    return v___x_3748_;
                }
                _ => {
                    let mut v___x_3749_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__4_3728_);
                    leanh::lean_dec(v_h__2_3726_);
                    v___x_3749_ = leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3749_;
                }
            }
        }
        4 => {
            leanh::lean_dec(v_h__6_3730_);
            leanh::lean_dec(v_h__4_3728_);
            leanh::lean_dec(v_h__3_3727_);
            leanh::lean_dec(v_h__1_3725_);
            match leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__5_3729_);
                    v_a_3750_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3750_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3751_ = leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3750_,
                        v_x_3724_,
                        leanh::lean_box(0),
                    );
                    return v___x_3751_;
                }
                4 => {
                    let mut v_a_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__2_3726_);
                    v_a_3752_ = leanh::lean_ctor_get(v_x_3721_, 0);
                    leanh::lean_inc(v_a_3752_);
                    leanh::lean_dec_ref_known(v_x_3721_, 1);
                    v_a_3753_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3753_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3754_ = leanh::lean_apply_4(
                        v_h__5_3729_,
                        v_a_3752_,
                        v_x_3722_,
                        v_a_3753_,
                        v_x_3724_,
                    );
                    return v___x_3754_;
                }
                _ => {
                    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__5_3729_);
                    leanh::lean_dec(v_h__2_3726_);
                    v___x_3755_ = leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3755_;
                }
            }
        }
        5 => {
            leanh::lean_dec(v_h__5_3729_);
            leanh::lean_dec(v_h__4_3728_);
            leanh::lean_dec(v_h__3_3727_);
            leanh::lean_dec(v_h__1_3725_);
            match leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__6_3730_);
                    v_a_3756_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3756_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3757_ = leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3756_,
                        v_x_3724_,
                        leanh::lean_box(0),
                    );
                    return v___x_3757_;
                }
                5 => {
                    let mut v_a_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__7_3731_);
                    leanh::lean_dec(v_h__2_3726_);
                    v_a_3758_ = leanh::lean_ctor_get(v_x_3721_, 0);
                    leanh::lean_inc(v_a_3758_);
                    leanh::lean_dec_ref_known(v_x_3721_, 1);
                    v_a_3759_ = leanh::lean_ctor_get(v_x_3723_, 0);
                    leanh::lean_inc(v_a_3759_);
                    leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3760_ = leanh::lean_apply_4(
                        v_h__6_3730_,
                        v_a_3758_,
                        v_x_3722_,
                        v_a_3759_,
                        v_x_3724_,
                    );
                    return v___x_3760_;
                }
                _ => {
                    let mut v___x_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_3730_);
                    leanh::lean_dec(v_h__2_3726_);
                    v___x_3761_ = leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_3761_;
                }
            }
        }
        _ => {
            leanh::lean_dec(v_h__6_3730_);
            leanh::lean_dec(v_h__5_3729_);
            leanh::lean_dec(v_h__4_3728_);
            leanh::lean_dec(v_h__3_3727_);
            leanh::lean_dec(v_h__1_3725_);
            if leanh::lean_obj_tag(v_x_3723_) == 1 {
                let mut v_a_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__7_3731_);
                v_a_3762_ = leanh::lean_ctor_get(v_x_3723_, 0);
                leanh::lean_inc(v_a_3762_);
                leanh::lean_dec_ref_known(v_x_3723_, 1);
                v___x_3763_ = leanh::lean_apply_5(
                    v_h__2_3726_,
                    v_x_3721_,
                    v_x_3722_,
                    v_a_3762_,
                    v_x_3724_,
                    leanh::lean_box(0),
                );
                return v___x_3763_;
            } else {
                let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_3726_);
                v___x_3764_ = leanh::lean_apply_10(
                    v_h__7_3731_,
                    v_x_3721_,
                    v_x_3722_,
                    v_x_3723_,
                    v_x_3724_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_3764_;
            }
        }
    }
}
pub unsafe fn l_Lean_Level_normLt(
    mut v_l_u2081_3765_: *mut leanh::LeanObject,
    mut v_l_u2082_3766_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    v___x_3767_ = leanh::lean_unsigned_to_nat(0);
    v___x_3768_ =
        l_Lean_Level_normLtAux(v_l_u2081_3765_, v___x_3767_, v_l_u2082_3766_, v___x_3767_);
    return v___x_3768_;
}
pub unsafe fn l_Lean_Level_normLt___boxed(
    mut v_l_u2081_3769_: *mut leanh::LeanObject,
    mut v_l_u2082_3770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3771_: u8 = 0;
    let mut v_r_3772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Lean_Level_normLt(v_l_u2081_3769_, v_l_u2082_3770_);
    leanh::lean_dec(v_l_u2082_3770_);
    leanh::lean_dec(v_l_u2081_3769_);
    v_r_3772_ = leanh::lean_box((v_res_3771_) as usize);
    return v_r_3772_;
}
pub unsafe fn l_Lean_Level_isAlreadyNormalizedCheap(
    mut v_x_3773_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: u8 = 0;
    let mut v_a_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_3773_) {
                0 => {
                    v___x_3774_ = 1;
                    return v___x_3774_;
                }
                4 => {
                    v___x_3775_ = 1;
                    return v___x_3775_;
                }
                5 => {
                    v___x_3776_ = 1;
                    return v___x_3776_;
                }
                1 => {
                    v_a_3777_ = leanh::lean_ctor_get(v_x_3773_, 0);
                    v_x_3773_ = v_a_3777_;
                    state = 0;
                    continue;
                }
                _ => {
                    v___x_3779_ = 0;
                    return v___x_3779_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_isAlreadyNormalizedCheap___boxed(
    mut v_x_3780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3781_: u8 = 0;
    let mut v_r_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_3780_);
    leanh::lean_dec(v_x_3780_);
    v_r_3782_ = leanh::lean_box((v_res_3781_) as usize);
    return v_r_3782_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_mkIMaxAux(
    mut v_x_3783_: *mut leanh::LeanObject,
    mut v_x_3784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_u2081_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_u2082_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3784_) == 0 {
                    leanh::lean_dec(v_x_3783_);
                    return v_x_3784_;
                } else {
                    match leanh::lean_obj_tag(v_x_3783_) {
                        0 => {
                            return v_x_3784_;
                        }
                        1 => {
                            v_a_3790_ = leanh::lean_ctor_get(v_x_3783_, 0);
                            if leanh::lean_obj_tag(v_a_3790_) == 0 {
                                leanh::lean_dec_ref_known(v_x_3783_, 1);
                                return v_x_3784_;
                            } else {
                                v_u_u2081_3786_ = v_x_3783_;
                                v_u_u2082_3787_ = v_x_3784_;
                                state = 1;
                                continue;
                            }
                        }
                        _ => {
                            v_u_u2081_3786_ = v_x_3783_;
                            v_u_u2082_3787_ = v_x_3784_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3788_ = lean_level_eq(v_u_u2081_3786_, v_u_u2082_3787_);
                if v___x_3788_ == 0 {
                    v___x_3789_ = l_Lean_Level_imax___override(v_u_u2081_3786_, v_u_u2082_3787_);
                    return v___x_3789_;
                } else {
                    leanh::lean_dec(v_u_u2082_3787_);
                    return v_u_u2081_3786_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(
    mut v_normalize_3791_: *mut leanh::LeanObject,
    mut v_x_3792_: *mut leanh::LeanObject,
    mut v_x_3793_: u8,
    mut v_x_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3792_) == 2 {
                    v_a_3795_ = leanh::lean_ctor_get(v_x_3792_, 0);
                    leanh::lean_inc(v_a_3795_);
                    v_a_3796_ = leanh::lean_ctor_get(v_x_3792_, 1);
                    leanh::lean_inc(v_a_3796_);
                    leanh::lean_dec_ref_known(v_x_3792_, 2);
                    leanh::lean_inc_ref(v_normalize_3791_);
                    v___x_3797_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(
                        v_normalize_3791_,
                        v_a_3795_,
                        v_x_3793_,
                        v_x_3794_,
                    );
                    v_x_3792_ = v_a_3796_;
                    v_x_3794_ = v___x_3797_;
                    state = 0;
                    continue;
                } else {
                    if v_x_3793_ == 0 {
                        leanh::lean_inc_ref(v_normalize_3791_);
                        v___x_3799_ = leanh::lean_apply_1(v_normalize_3791_, v_x_3792_);
                        v___x_3800_ = 1;
                        v_x_3792_ = v___x_3799_;
                        v_x_3793_ = v___x_3800_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_normalize_3791_);
                        v___x_3802_ = lean_array_push(v_x_3794_, v_x_3792_);
                        return v___x_3802_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___boxed(
    mut v_normalize_3803_: *mut leanh::LeanObject,
    mut v_x_3804_: *mut leanh::LeanObject,
    mut v_x_3805_: *mut leanh::LeanObject,
    mut v_x_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3807_ = (leanh::lean_unbox(v_x_3805_) as u8);
    v_res_3808_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(
        v_normalize_3803_,
        v_x_3804_,
        v_x_36__boxed_3807_,
        v_x_3806_,
    );
    return v_res_3808_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_accMax(
    mut v_result_3809_: *mut leanh::LeanObject,
    mut v_prev_3810_: *mut leanh::LeanObject,
    mut v_offset_3811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3812_: u8 = 0;
    v___x_3812_ = l_Lean_Level_isZero(v_result_3809_);
    if v___x_3812_ == 0 {
        let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3813_ = l_Lean_Level_addOffsetAux(v_offset_3811_, v_prev_3810_);
        v___x_3814_ = l_Lean_Level_max___override(v_result_3809_, v___x_3813_);
        return v___x_3814_;
    } else {
        let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_result_3809_);
        v___x_3815_ = l_Lean_Level_addOffsetAux(v_offset_3811_, v_prev_3810_);
        return v___x_3815_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_mkMaxAux(
    mut v_lvls_3816_: *mut leanh::LeanObject,
    mut v_extraK_3817_: *mut leanh::LeanObject,
    mut v_i_3818_: *mut leanh::LeanObject,
    mut v_prev_3819_: *mut leanh::LeanObject,
    mut v_prevK_3820_: *mut leanh::LeanObject,
    mut v_result_3821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currK_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3822_ = lean_array_get_size(v_lvls_3816_);
                v___x_3823_ = lean_nat_dec_lt(v_i_3818_, v___x_3822_);
                if v___x_3823_ == 0 {
                    leanh::lean_dec(v_i_3818_);
                    v___x_3824_ = lean_nat_add(v_extraK_3817_, v_prevK_3820_);
                    leanh::lean_dec(v_prevK_3820_);
                    v___x_3825_ = l___private_Lean_Level_0__Lean_Level_accMax(
                        v_result_3821_,
                        v_prev_3819_,
                        v___x_3824_,
                    );
                    return v___x_3825_;
                } else {
                    v_lvl_3826_ = lean_array_fget_borrowed(v_lvls_3816_, v_i_3818_);
                    v_curr_3827_ = l_Lean_Level_getLevelOffset(v_lvl_3826_);
                    v_currK_3828_ = l_Lean_Level_getOffset(v_lvl_3826_);
                    v___x_3829_ = lean_level_eq(v_curr_3827_, v_prev_3819_);
                    if v___x_3829_ == 0 {
                        v___x_3830_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3831_ = lean_nat_add(v_i_3818_, v___x_3830_);
                        leanh::lean_dec(v_i_3818_);
                        v___x_3832_ = lean_nat_add(v_extraK_3817_, v_prevK_3820_);
                        leanh::lean_dec(v_prevK_3820_);
                        v___x_3833_ = l___private_Lean_Level_0__Lean_Level_accMax(
                            v_result_3821_,
                            v_prev_3819_,
                            v___x_3832_,
                        );
                        v_i_3818_ = v___x_3831_;
                        v_prev_3819_ = v_curr_3827_;
                        v_prevK_3820_ = v_currK_3828_;
                        v_result_3821_ = v___x_3833_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_prevK_3820_);
                        leanh::lean_dec(v_prev_3819_);
                        v___x_3835_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3836_ = lean_nat_add(v_i_3818_, v___x_3835_);
                        leanh::lean_dec(v_i_3818_);
                        v_i_3818_ = v___x_3836_;
                        v_prev_3819_ = v_curr_3827_;
                        v_prevK_3820_ = v_currK_3828_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_mkMaxAux___boxed(
    mut v_lvls_3838_: *mut leanh::LeanObject,
    mut v_extraK_3839_: *mut leanh::LeanObject,
    mut v_i_3840_: *mut leanh::LeanObject,
    mut v_prev_3841_: *mut leanh::LeanObject,
    mut v_prevK_3842_: *mut leanh::LeanObject,
    mut v_result_3843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3844_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(
        v_lvls_3838_,
        v_extraK_3839_,
        v_i_3840_,
        v_prev_3841_,
        v_prevK_3842_,
        v_result_3843_,
    );
    leanh::lean_dec(v_extraK_3839_);
    leanh::lean_dec_ref(v_lvls_3838_);
    return v_res_3844_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_skipExplicit(
    mut v_lvls_3845_: *mut leanh::LeanObject,
    mut v_i_3846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v_lvl_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3847_ = lean_array_get_size(v_lvls_3845_);
                v___x_3848_ = lean_nat_dec_lt(v_i_3846_, v___x_3847_);
                if v___x_3848_ == 0 {
                    return v_i_3846_;
                } else {
                    v_lvl_3849_ = lean_array_fget_borrowed(v_lvls_3845_, v_i_3846_);
                    v___x_3850_ = l_Lean_Level_getLevelOffset(v_lvl_3849_);
                    v___x_3851_ = l_Lean_Level_isZero(v___x_3850_);
                    leanh::lean_dec(v___x_3850_);
                    if v___x_3851_ == 0 {
                        return v_i_3846_;
                    } else {
                        v___x_3852_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3853_ = lean_nat_add(v_i_3846_, v___x_3852_);
                        leanh::lean_dec(v_i_3846_);
                        v_i_3846_ = v___x_3853_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_skipExplicit___boxed(
    mut v_lvls_3855_: *mut leanh::LeanObject,
    mut v_i_3856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3857_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_3855_, v_i_3856_);
    leanh::lean_dec_ref(v_lvls_3855_);
    return v_res_3857_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
    mut v_lvls_3858_: *mut leanh::LeanObject,
    mut v_maxExplicit_3859_: *mut leanh::LeanObject,
    mut v_i_3860_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v_lvl_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = lean_array_get_size(v_lvls_3858_);
                v___x_3862_ = lean_nat_dec_lt(v_i_3860_, v___x_3861_);
                if v___x_3862_ == 0 {
                    leanh::lean_dec(v_i_3860_);
                    return v___x_3862_;
                } else {
                    v_lvl_3863_ = lean_array_fget_borrowed(v_lvls_3858_, v_i_3860_);
                    v___x_3864_ = l_Lean_Level_getOffset(v_lvl_3863_);
                    v___x_3865_ = lean_nat_dec_le(v_maxExplicit_3859_, v___x_3864_);
                    leanh::lean_dec(v___x_3864_);
                    if v___x_3865_ == 0 {
                        v___x_3866_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3867_ = lean_nat_add(v_i_3860_, v___x_3866_);
                        leanh::lean_dec(v_i_3860_);
                        v_i_3860_ = v___x_3867_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_3860_);
                        return v___x_3865_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(
    mut v_lvls_3869_: *mut leanh::LeanObject,
    mut v_maxExplicit_3870_: *mut leanh::LeanObject,
    mut v_i_3871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3872_: u8 = 0;
    let mut v_r_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
        v_lvls_3869_,
        v_maxExplicit_3870_,
        v_i_3871_,
    );
    leanh::lean_dec(v_maxExplicit_3870_);
    leanh::lean_dec_ref(v_lvls_3869_);
    v_r_3873_ = leanh::lean_box((v_res_3872_) as usize);
    return v_r_3873_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
    mut v_lvls_3874_: *mut leanh::LeanObject,
    mut v_firstNonExplicit_3875_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    v___x_3876_ = leanh::lean_unsigned_to_nat(0);
    v___x_3877_ = lean_nat_dec_eq(v_firstNonExplicit_3875_, v___x_3876_);
    if v___x_3877_ == 0 {
        let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_max_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: u8 = 0;
        v___x_3878_ = leanh::lean_box(0);
        v___x_3879_ = leanh::lean_unsigned_to_nat(1);
        v___x_3880_ = lean_nat_sub(v_firstNonExplicit_3875_, v___x_3879_);
        v___x_3881_ = lean_array_get_borrowed(v___x_3878_, v_lvls_3874_, v___x_3880_);
        leanh::lean_dec(v___x_3880_);
        v_max_3882_ = l_Lean_Level_getOffset(v___x_3881_);
        v___x_3883_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
            v_lvls_3874_,
            v_max_3882_,
            v_firstNonExplicit_3875_,
        );
        leanh::lean_dec(v_max_3882_);
        return v___x_3883_;
    } else {
        let mut v___x_3884_: u8 = 0;
        leanh::lean_dec(v_firstNonExplicit_3875_);
        v___x_3884_ = 0;
        return v___x_3884_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(
    mut v_lvls_3885_: *mut leanh::LeanObject,
    mut v_firstNonExplicit_3886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
        v_lvls_3885_,
        v_firstNonExplicit_3886_,
    );
    leanh::lean_dec_ref(v_lvls_3885_);
    v_r_3888_ = leanh::lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_panic___at___00Lean_Level_normalize_spec__2(
    mut v_msg_3889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = leanh::lean_box(0);
    v___x_3891_ = lean_panic_fn_borrowed(v___x_3890_, v_msg_3889_);
    return v___x_3891_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(
    mut v_hi_3892_: *mut leanh::LeanObject,
    mut v_pivot_3893_: *mut leanh::LeanObject,
    mut v_as_3894_: *mut leanh::LeanObject,
    mut v_i_3895_: *mut leanh::LeanObject,
    mut v_k_3896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3897_ = lean_nat_dec_lt(v_k_3896_, v_hi_3892_);
                if v___x_3897_ == 0 {
                    leanh::lean_dec(v_k_3896_);
                    v___x_3898_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_hi_3892_);
                    v___x_3899_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3899_, 0, v_i_3895_);
                    leanh::lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                    return v___x_3899_;
                } else {
                    v___x_3900_ = lean_array_fget_borrowed(v_as_3894_, v_k_3896_);
                    v___x_3901_ = l_Lean_Level_normLt(v___x_3900_, v_pivot_3893_);
                    if v___x_3901_ == 0 {
                        v___x_3902_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3903_ = lean_nat_add(v_k_3896_, v___x_3902_);
                        leanh::lean_dec(v_k_3896_);
                        v_k_3896_ = v___x_3903_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3905_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_k_3896_);
                        v___x_3906_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3907_ = lean_nat_add(v_i_3895_, v___x_3906_);
                        leanh::lean_dec(v_i_3895_);
                        v___x_3908_ = lean_nat_add(v_k_3896_, v___x_3906_);
                        leanh::lean_dec(v_k_3896_);
                        v_as_3894_ = v___x_3905_;
                        v_i_3895_ = v___x_3907_;
                        v_k_3896_ = v___x_3908_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg___boxed(
    mut v_hi_3910_: *mut leanh::LeanObject,
    mut v_pivot_3911_: *mut leanh::LeanObject,
    mut v_as_3912_: *mut leanh::LeanObject,
    mut v_i_3913_: *mut leanh::LeanObject,
    mut v_k_3914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_3910_, v_pivot_3911_, v_as_3912_, v_i_3913_, v_k_3914_);
    leanh::lean_dec(v_pivot_3911_);
    leanh::lean_dec(v_hi_3910_);
    return v_res_3915_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(
    mut v_n_3916_: *mut leanh::LeanObject,
    mut v_as_3917_: *mut leanh::LeanObject,
    mut v_lo_3918_: *mut leanh::LeanObject,
    mut v_hi_3919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3931_ = lean_nat_dec_lt(v_lo_3918_, v_hi_3919_);
                if v___x_3931_ == 0 {
                    leanh::lean_dec(v_lo_3918_);
                    return v_as_3917_;
                } else {
                    v___x_3932_ = lean_nat_add(v_lo_3918_, v_hi_3919_);
                    v___x_3933_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_3934_ = lean_nat_shiftr(v___x_3932_, v___x_3933_);
                    leanh::lean_dec(v___x_3932_);
                    v___x_3947_ = lean_array_fget_borrowed(v_as_3917_, v_mid_3934_);
                    v___x_3948_ = lean_array_fget_borrowed(v_as_3917_, v_lo_3918_);
                    v___x_3949_ = l_Lean_Level_normLt(v___x_3947_, v___x_3948_);
                    if v___x_3949_ == 0 {
                        v___y_3942_ = v_as_3917_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3950_ = lean_array_fswap(v_as_3917_, v_lo_3918_, v_mid_3934_);
                        v___y_3942_ = v___x_3950_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_3922_ = lean_array_fget(v___y_3921_, v_hi_3919_);
                leanh::lean_inc_n(v_lo_3918_, 2);
                v___x_3923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_3919_, v_pivot_3922_, v___y_3921_, v_lo_3918_, v_lo_3918_);
                leanh::lean_dec(v_pivot_3922_);
                v_fst_3924_ = leanh::lean_ctor_get(v___x_3923_, 0);
                leanh::lean_inc(v_fst_3924_);
                v_snd_3925_ = leanh::lean_ctor_get(v___x_3923_, 1);
                leanh::lean_inc(v_snd_3925_);
                leanh::lean_dec_ref(v___x_3923_);
                v___x_3926_ = lean_nat_dec_le(v_hi_3919_, v_fst_3924_);
                if v___x_3926_ == 0 {
                    v___x_3927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_3916_, v_snd_3925_, v_lo_3918_, v_fst_3924_);
                    v___x_3928_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3929_ = lean_nat_add(v_fst_3924_, v___x_3928_);
                    leanh::lean_dec(v_fst_3924_);
                    v_as_3917_ = v___x_3927_;
                    v_lo_3918_ = v___x_3929_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_3924_);
                    leanh::lean_dec(v_lo_3918_);
                    return v_snd_3925_;
                }
            }
            2 => {
                v___x_3937_ = lean_array_fget_borrowed(v___y_3936_, v_mid_3934_);
                v___x_3938_ = lean_array_fget_borrowed(v___y_3936_, v_hi_3919_);
                v___x_3939_ = l_Lean_Level_normLt(v___x_3937_, v___x_3938_);
                if v___x_3939_ == 0 {
                    leanh::lean_dec(v_mid_3934_);
                    v___y_3921_ = v___y_3936_;
                    state = 1;
                    continue;
                } else {
                    v___x_3940_ = lean_array_fswap(v___y_3936_, v_mid_3934_, v_hi_3919_);
                    leanh::lean_dec(v_mid_3934_);
                    v___y_3921_ = v___x_3940_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3943_ = lean_array_fget_borrowed(v___y_3942_, v_hi_3919_);
                v___x_3944_ = lean_array_fget_borrowed(v___y_3942_, v_lo_3918_);
                v___x_3945_ = l_Lean_Level_normLt(v___x_3943_, v___x_3944_);
                if v___x_3945_ == 0 {
                    v___y_3936_ = v___y_3942_;
                    state = 2;
                    continue;
                } else {
                    v___x_3946_ = lean_array_fswap(v___y_3942_, v_lo_3918_, v_hi_3919_);
                    v___y_3936_ = v___x_3946_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg___boxed(
    mut v_n_3951_: *mut leanh::LeanObject,
    mut v_as_3952_: *mut leanh::LeanObject,
    mut v_lo_3953_: *mut leanh::LeanObject,
    mut v_hi_3954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_3951_, v_as_3952_, v_lo_3953_, v_hi_3954_);
    leanh::lean_dec(v_hi_3954_);
    leanh::lean_dec(v_n_3951_);
    return v_res_3955_;
}
pub unsafe fn _init_l_Lean_Level_normalize___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_3960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_Level_normalize___closed__2;
    v___x_3961_ = leanh::lean_unsigned_to_nat(11);
    v___x_3962_ = leanh::lean_unsigned_to_nat(401);
    v___x_3963_ = l_Lean_Level_normalize___closed__1;
    v___x_3964_ = l_Lean_Level_mvarId_x21___closed__0;
    v___x_3965_ = l_mkPanicMessageWithDecl(
        v___x_3964_,
        v___x_3963_,
        v___x_3962_,
        v___x_3961_,
        v___x_3960_,
    );
    return v___x_3965_;
}
pub unsafe fn l_Lean_Level_normalize(
    mut v_l_3966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3967_: u8 = 0;
    let mut v_k_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvls_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvls_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_u2081_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevK_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_firstNonExplicit_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: u8 = 0;
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: u8 = 0;
    let mut v___x_4001_: u8 = 0;
    let mut v_a_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    let mut v_l_u2081_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3967_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_3966_);
                if v___x_3967_ == 0 {
                    v_k_3968_ = l_Lean_Level_getOffset(v_l_3966_);
                    v_u_3969_ = l_Lean_Level_getLevelOffset(v_l_3966_);
                    match leanh::lean_obj_tag(v_u_3969_) {
                        2 => {
                            v_a_3970_ = leanh::lean_ctor_get(v_u_3969_, 0);
                            leanh::lean_inc(v_a_3970_);
                            v_a_3971_ = leanh::lean_ctor_get(v_u_3969_, 1);
                            leanh::lean_inc(v_a_3971_);
                            leanh::lean_dec_ref_known(v_u_3969_, 2);
                            v___x_3972_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3973_ = l_Lean_Level_normalize___closed__0;
                            v_lvls_3974_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_3970_, v___x_3967_, v___x_3973_);
                            v_lvls_3975_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_3971_, v___x_3967_, v_lvls_3974_);
                            v___x_3976_ = leanh::lean_unsigned_to_nat(1);
                            v___x_3991_ = lean_array_get_size(v_lvls_3975_);
                            v___x_3996_ = lean_nat_dec_eq(v___x_3991_, v___x_3972_);
                            if v___x_3996_ == 0 {
                                v___x_3997_ = lean_nat_sub(v___x_3991_, v___x_3976_);
                                v___x_4001_ = lean_nat_dec_le(v___x_3972_, v___x_3997_);
                                if v___x_4001_ == 0 {
                                    leanh::lean_inc(v___x_3997_);
                                    v___y_3999_ = v___x_3997_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___y_3999_ = v___x_3972_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___y_3987_ = v_lvls_3975_;
                                state = 2;
                                continue;
                            }
                        }
                        3 => {
                            v_a_4002_ = leanh::lean_ctor_get(v_u_3969_, 0);
                            leanh::lean_inc(v_a_4002_);
                            v_a_4003_ = leanh::lean_ctor_get(v_u_3969_, 1);
                            leanh::lean_inc(v_a_4003_);
                            leanh::lean_dec_ref_known(v_u_3969_, 2);
                            v___x_4004_ = l_Lean_Level_isNeverZero(v_a_4003_);
                            if v___x_4004_ == 0 {
                                v_l_u2081_4005_ = l_Lean_Level_normalize(v_a_4002_);
                                leanh::lean_dec(v_a_4002_);
                                v_l_u2082_4006_ = l_Lean_Level_normalize(v_a_4003_);
                                leanh::lean_dec(v_a_4003_);
                                v___x_4007_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(
                                    v_l_u2081_4005_,
                                    v_l_u2082_4006_,
                                );
                                v___x_4008_ = l_Lean_Level_addOffsetAux(v_k_3968_, v___x_4007_);
                                return v___x_4008_;
                            } else {
                                v___x_4009_ = l_Lean_Level_max___override(v_a_4002_, v_a_4003_);
                                v___x_4010_ = l_Lean_Level_normalize(v___x_4009_);
                                leanh::lean_dec(v___x_4009_);
                                v___x_4011_ = l_Lean_Level_addOffsetAux(v_k_3968_, v___x_4010_);
                                return v___x_4011_;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_u_3969_);
                            leanh::lean_dec(v_k_3968_);
                            v___x_4012_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_Lean_Level_normalize___closed__3),
                                core::ptr::addr_of_mut!(l_Lean_Level_normalize___closed__3_once),
                                _init_l_Lean_Level_normalize___closed__3,
                            );
                            v___x_4013_ =
                                l_panic___at___00Lean_Level_normalize_spec__2(v___x_4012_);
                            return v___x_4013_;
                        }
                    }
                } else {
                    leanh::lean_inc(v_l_3966_);
                    return v_l_3966_;
                }
            }
            1 => {
                v___x_3980_ = leanh::lean_box(0);
                v_lvl_u2081_3981_ = lean_array_get_borrowed(v___x_3980_, v___y_3978_, v___y_3979_);
                v_prev_3982_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_3981_);
                v_prevK_3983_ = l_Lean_Level_getOffset(v_lvl_u2081_3981_);
                v___x_3984_ = lean_nat_add(v___y_3979_, v___x_3976_);
                leanh::lean_dec(v___y_3979_);
                v___x_3985_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(
                    v___y_3978_,
                    v_k_3968_,
                    v___x_3984_,
                    v_prev_3982_,
                    v_prevK_3983_,
                    v___x_3980_,
                );
                leanh::lean_dec(v_k_3968_);
                leanh::lean_dec_ref(v___y_3978_);
                return v___x_3985_;
            }
            2 => {
                v_firstNonExplicit_3988_ =
                    l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_3987_, v___x_3972_);
                leanh::lean_inc(v_firstNonExplicit_3988_);
                v___x_3989_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
                    v___y_3987_,
                    v_firstNonExplicit_3988_,
                );
                if v___x_3989_ == 0 {
                    v___x_3990_ = lean_nat_sub(v_firstNonExplicit_3988_, v___x_3976_);
                    leanh::lean_dec(v_firstNonExplicit_3988_);
                    v___y_3978_ = v___y_3987_;
                    v___y_3979_ = v___x_3990_;
                    state = 1;
                    continue;
                } else {
                    v___y_3978_ = v___y_3987_;
                    v___y_3979_ = v_firstNonExplicit_3988_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_3995_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v___x_3991_, v_lvls_3975_, v___y_3993_, v___y_3994_);
                leanh::lean_dec(v___y_3994_);
                v___y_3987_ = v___x_3995_;
                state = 2;
                continue;
            }
            4 => {
                v___x_4000_ = lean_nat_dec_le(v___y_3999_, v___x_3997_);
                if v___x_4000_ == 0 {
                    leanh::lean_dec(v___x_3997_);
                    leanh::lean_inc(v___y_3999_);
                    v___y_3993_ = v___y_3999_;
                    v___y_3994_ = v___y_3999_;
                    state = 3;
                    continue;
                } else {
                    v___y_3993_ = v___y_3999_;
                    v___y_3994_ = v___x_3997_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(
    mut v_x_4014_: *mut leanh::LeanObject,
    mut v_x_4015_: u8,
    mut v_x_4016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4014_) == 2 {
                    v_a_4017_ = leanh::lean_ctor_get(v_x_4014_, 0);
                    leanh::lean_inc(v_a_4017_);
                    v_a_4018_ = leanh::lean_ctor_get(v_x_4014_, 1);
                    leanh::lean_inc(v_a_4018_);
                    leanh::lean_dec_ref_known(v_x_4014_, 2);
                    v___x_4019_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_4017_, v_x_4015_, v_x_4016_);
                    v_x_4014_ = v_a_4018_;
                    v_x_4016_ = v___x_4019_;
                    state = 0;
                    continue;
                } else {
                    if v_x_4015_ == 0 {
                        v___x_4021_ = l_Lean_Level_normalize(v_x_4014_);
                        leanh::lean_dec(v_x_4014_);
                        v___x_4022_ = 1;
                        v_x_4014_ = v___x_4021_;
                        v_x_4015_ = v___x_4022_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4024_ = lean_array_push(v_x_4016_, v_x_4014_);
                        return v___x_4024_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0___boxed(
    mut v_x_4025_: *mut leanh::LeanObject,
    mut v_x_4026_: *mut leanh::LeanObject,
    mut v_x_4027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_676__boxed_4028_: u8 = 0;
    let mut v_res_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_676__boxed_4028_ = (leanh::lean_unbox(v_x_4026_) as u8);
    v_res_4029_ =
        l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(
            v_x_4025_,
            v_x_676__boxed_4028_,
            v_x_4027_,
        );
    return v_res_4029_;
}
pub unsafe fn l_Lean_Level_normalize___boxed(
    mut v_l_4030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Lean_Level_normalize(v_l_4030_);
    leanh::lean_dec(v_l_4030_);
    return v_res_4031_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(
    mut v_n_4032_: *mut leanh::LeanObject,
    mut v_as_4033_: *mut leanh::LeanObject,
    mut v_lo_4034_: *mut leanh::LeanObject,
    mut v_hi_4035_: *mut leanh::LeanObject,
    mut v_w_4036_: *mut leanh::LeanObject,
    mut v_hlo_4037_: *mut leanh::LeanObject,
    mut v_hhi_4038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_4032_, v_as_4033_, v_lo_4034_, v_hi_4035_);
    return v___x_4039_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(
    mut v_n_4040_: *mut leanh::LeanObject,
    mut v_as_4041_: *mut leanh::LeanObject,
    mut v_lo_4042_: *mut leanh::LeanObject,
    mut v_hi_4043_: *mut leanh::LeanObject,
    mut v_w_4044_: *mut leanh::LeanObject,
    mut v_hlo_4045_: *mut leanh::LeanObject,
    mut v_hhi_4046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_4040_, v_as_4041_, v_lo_4042_, v_hi_4043_, v_w_4044_, v_hlo_4045_, v_hhi_4046_);
    leanh::lean_dec(v_hi_4043_);
    leanh::lean_dec(v_n_4040_);
    return v_res_4047_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(
    mut v_n_4048_: *mut leanh::LeanObject,
    mut v_lo_4049_: *mut leanh::LeanObject,
    mut v_hi_4050_: *mut leanh::LeanObject,
    mut v_hhi_4051_: *mut leanh::LeanObject,
    mut v_pivot_4052_: *mut leanh::LeanObject,
    mut v_as_4053_: *mut leanh::LeanObject,
    mut v_i_4054_: *mut leanh::LeanObject,
    mut v_k_4055_: *mut leanh::LeanObject,
    mut v_ilo_4056_: *mut leanh::LeanObject,
    mut v_ik_4057_: *mut leanh::LeanObject,
    mut v_w_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_4050_, v_pivot_4052_, v_as_4053_, v_i_4054_, v_k_4055_);
    return v___x_4059_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(
    mut v_n_4060_: *mut leanh::LeanObject,
    mut v_lo_4061_: *mut leanh::LeanObject,
    mut v_hi_4062_: *mut leanh::LeanObject,
    mut v_hhi_4063_: *mut leanh::LeanObject,
    mut v_pivot_4064_: *mut leanh::LeanObject,
    mut v_as_4065_: *mut leanh::LeanObject,
    mut v_i_4066_: *mut leanh::LeanObject,
    mut v_k_4067_: *mut leanh::LeanObject,
    mut v_ilo_4068_: *mut leanh::LeanObject,
    mut v_ik_4069_: *mut leanh::LeanObject,
    mut v_w_4070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_4060_, v_lo_4061_, v_hi_4062_, v_hhi_4063_, v_pivot_4064_, v_as_4065_, v_i_4066_, v_k_4067_, v_ilo_4068_, v_ik_4069_, v_w_4070_);
    leanh::lean_dec(v_pivot_4064_);
    leanh::lean_dec(v_hi_4062_);
    leanh::lean_dec(v_lo_4061_);
    leanh::lean_dec(v_n_4060_);
    return v_res_4071_;
}
pub unsafe fn l_Lean_Level_isEquiv(
    mut v_u_4072_: *mut leanh::LeanObject,
    mut v_v_4073_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4074_: u8 = 0;
    v___x_4074_ = lean_level_eq(v_u_4072_, v_v_4073_);
    if v___x_4074_ == 0 {
        let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: u8 = 0;
        v___x_4075_ = l_Lean_Level_normalize(v_u_4072_);
        v___x_4076_ = l_Lean_Level_normalize(v_v_4073_);
        v___x_4077_ = lean_level_eq(v___x_4075_, v___x_4076_);
        leanh::lean_dec(v___x_4076_);
        leanh::lean_dec(v___x_4075_);
        return v___x_4077_;
    } else {
        return v___x_4074_;
    }
}
pub unsafe fn l_Lean_Level_isEquiv___boxed(
    mut v_u_4078_: *mut leanh::LeanObject,
    mut v_v_4079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4080_: u8 = 0;
    let mut v_r_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Level_isEquiv(v_u_4078_, v_v_4079_);
    leanh::lean_dec(v_v_4079_);
    leanh::lean_dec(v_u_4078_);
    v_r_4081_ = leanh::lean_box((v_res_4080_) as usize);
    return v_r_4081_;
}
pub unsafe fn l_Lean_Level_dec(
    mut v_x_4082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_l_u2081_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4082_) {
                0 => {
                    v___x_4098_ = leanh::lean_box(0);
                    return v___x_4098_;
                }
                1 => {
                    v_a_4099_ = leanh::lean_ctor_get(v_x_4082_, 0);
                    leanh::lean_inc(v_a_4099_);
                    v___x_4100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4100_, 0, v_a_4099_);
                    return v___x_4100_;
                }
                2 => {
                    v_a_4101_ = leanh::lean_ctor_get(v_x_4082_, 0);
                    v_a_4102_ = leanh::lean_ctor_get(v_x_4082_, 1);
                    v_l_u2081_4084_ = v_a_4101_;
                    v_l_u2082_4085_ = v_a_4102_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_4103_ = leanh::lean_ctor_get(v_x_4082_, 0);
                    v_a_4104_ = leanh::lean_ctor_get(v_x_4082_, 1);
                    v_l_u2081_4084_ = v_a_4103_;
                    v_l_u2082_4085_ = v_a_4104_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___x_4105_ = leanh::lean_box(0);
                    return v___x_4105_;
                }
            },
            1 => {
                v___x_4086_ = l_Lean_Level_dec(v_l_u2081_4084_);
                if leanh::lean_obj_tag(v___x_4086_) == 0 {
                    return v___x_4086_;
                } else {
                    v_val_4087_ = leanh::lean_ctor_get(v___x_4086_, 0);
                    leanh::lean_inc(v_val_4087_);
                    leanh::lean_dec_ref_known(v___x_4086_, 1);
                    v___x_4088_ = l_Lean_Level_dec(v_l_u2082_4085_);
                    if leanh::lean_obj_tag(v___x_4088_) == 0 {
                        leanh::lean_dec(v_val_4087_);
                        return v___x_4088_;
                    } else {
                        v_val_4089_ = leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4097_ =
                            (!leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4097_ == 0 {
                            v___x_4091_ = v___x_4088_;
                            v_isShared_4092_ = v_isSharedCheck_4097_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4089_);
                            leanh::lean_dec(v___x_4088_);
                            v___x_4091_ = leanh::lean_box(0);
                            v_isShared_4092_ = v_isSharedCheck_4097_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_4093_ = l_Lean_Level_max___override(v_val_4087_, v_val_4089_);
                if v_isShared_4092_ == 0 {
                    leanh::lean_ctor_set(v___x_4091_, 0, v___x_4093_);
                    v___x_4095_ = v___x_4091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
                    v___x_4095_ = v_reuseFailAlloc_4096_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_dec___boxed(
    mut v_x_4106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4107_ = l_Lean_Level_dec(v_x_4106_);
    leanh::lean_dec(v_x_4106_);
    return v_res_4107_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorIdx(
    mut v_x_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_4108_) {
        0 => {
            let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4109_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4109_;
        }
        1 => {
            let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4110_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4110_;
        }
        2 => {
            let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4111_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4111_;
        }
        3 => {
            let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4112_ = leanh::lean_unsigned_to_nat(3);
            return v___x_4112_;
        }
        _ => {
            let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4113_ = leanh::lean_unsigned_to_nat(4);
            return v___x_4113_;
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_ctorIdx___boxed(
    mut v_x_4114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_Lean_Level_PP_Result_ctorIdx(v_x_4114_);
    leanh::lean_dec_ref(v_x_4114_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim___redArg(
    mut v_t_4116_: *mut leanh::LeanObject,
    mut v_k_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_4116_) == 2 {
        let mut v_a_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4118_ = leanh::lean_ctor_get(v_t_4116_, 0);
        leanh::lean_inc_ref(v_a_4118_);
        v_a_4119_ = leanh::lean_ctor_get(v_t_4116_, 1);
        leanh::lean_inc(v_a_4119_);
        leanh::lean_dec_ref_known(v_t_4116_, 2);
        v___x_4120_ = leanh::lean_apply_2(v_k_4117_, v_a_4118_, v_a_4119_);
        return v___x_4120_;
    } else {
        let mut v_a_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4121_ = leanh::lean_ctor_get(v_t_4116_, 0);
        leanh::lean_inc(v_a_4121_);
        leanh::lean_dec_ref(v_t_4116_);
        v___x_4122_ = leanh::lean_apply_1(v_k_4117_, v_a_4121_);
        return v___x_4122_;
    }
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim(
    mut v_motive__1_4123_: *mut leanh::LeanObject,
    mut v_ctorIdx_4124_: *mut leanh::LeanObject,
    mut v_t_4125_: *mut leanh::LeanObject,
    mut v_h_4126_: *mut leanh::LeanObject,
    mut v_k_4127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4125_, v_k_4127_);
    return v___x_4128_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim___boxed(
    mut v_motive__1_4129_: *mut leanh::LeanObject,
    mut v_ctorIdx_4130_: *mut leanh::LeanObject,
    mut v_t_4131_: *mut leanh::LeanObject,
    mut v_h_4132_: *mut leanh::LeanObject,
    mut v_k_4133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_Level_PP_Result_ctorElim(
        v_motive__1_4129_,
        v_ctorIdx_4130_,
        v_t_4131_,
        v_h_4132_,
        v_k_4133_,
    );
    leanh::lean_dec(v_ctorIdx_4130_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_Level_PP_Result_leaf_elim___redArg(
    mut v_t_4135_: *mut leanh::LeanObject,
    mut v_leaf_4136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4135_, v_leaf_4136_);
    return v___x_4137_;
}
pub unsafe fn l_Lean_Level_PP_Result_leaf_elim(
    mut v_motive__1_4138_: *mut leanh::LeanObject,
    mut v_t_4139_: *mut leanh::LeanObject,
    mut v_h_4140_: *mut leanh::LeanObject,
    mut v_leaf_4141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4139_, v_leaf_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_Level_PP_Result_num_elim___redArg(
    mut v_t_4143_: *mut leanh::LeanObject,
    mut v_num_4144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4143_, v_num_4144_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_Level_PP_Result_num_elim(
    mut v_motive__1_4146_: *mut leanh::LeanObject,
    mut v_t_4147_: *mut leanh::LeanObject,
    mut v_h_4148_: *mut leanh::LeanObject,
    mut v_num_4149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4147_, v_num_4149_);
    return v___x_4150_;
}
pub unsafe fn l_Lean_Level_PP_Result_offset_elim___redArg(
    mut v_t_4151_: *mut leanh::LeanObject,
    mut v_offset_4152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4151_, v_offset_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Lean_Level_PP_Result_offset_elim(
    mut v_motive__1_4154_: *mut leanh::LeanObject,
    mut v_t_4155_: *mut leanh::LeanObject,
    mut v_h_4156_: *mut leanh::LeanObject,
    mut v_offset_4157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4158_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4155_, v_offset_4157_);
    return v___x_4158_;
}
pub unsafe fn l_Lean_Level_PP_Result_maxNode_elim___redArg(
    mut v_t_4159_: *mut leanh::LeanObject,
    mut v_maxNode_4160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4161_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4159_, v_maxNode_4160_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_Level_PP_Result_maxNode_elim(
    mut v_motive__1_4162_: *mut leanh::LeanObject,
    mut v_t_4163_: *mut leanh::LeanObject,
    mut v_h_4164_: *mut leanh::LeanObject,
    mut v_maxNode_4165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4163_, v_maxNode_4165_);
    return v___x_4166_;
}
pub unsafe fn l_Lean_Level_PP_Result_imaxNode_elim___redArg(
    mut v_t_4167_: *mut leanh::LeanObject,
    mut v_imaxNode_4168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4169_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4167_, v_imaxNode_4168_);
    return v___x_4169_;
}
pub unsafe fn l_Lean_Level_PP_Result_imaxNode_elim(
    mut v_motive__1_4170_: *mut leanh::LeanObject,
    mut v_t_4171_: *mut leanh::LeanObject,
    mut v_h_4172_: *mut leanh::LeanObject,
    mut v_imaxNode_4173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4171_, v_imaxNode_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Level_PP_Result_succ(
    mut v_x_4175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut v_a_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4175_) {
                2 => {
                    v_a_4176_ = leanh::lean_ctor_get(v_x_4175_, 0);
                    v_a_4177_ = leanh::lean_ctor_get(v_x_4175_, 1);
                    v_isSharedCheck_4186_ = (!leanh::lean_is_exclusive(v_x_4175_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4179_ = v_x_4175_;
                        v_isShared_4180_ = v_isSharedCheck_4186_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4177_);
                        leanh::lean_inc(v_a_4176_);
                        leanh::lean_dec(v_x_4175_);
                        v___x_4179_ = leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4186_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4187_ = leanh::lean_ctor_get(v_x_4175_, 0);
                    v_isSharedCheck_4196_ = (!leanh::lean_is_exclusive(v_x_4175_)) as u8;
                    if v_isSharedCheck_4196_ == 0 {
                        v___x_4189_ = v_x_4175_;
                        v_isShared_4190_ = v_isSharedCheck_4196_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4187_);
                        leanh::lean_dec(v_x_4175_);
                        v___x_4189_ = leanh::lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4196_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_4197_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4198_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4198_, 0, v_x_4175_);
                    leanh::lean_ctor_set(v___x_4198_, 1, v___x_4197_);
                    return v___x_4198_;
                }
            },
            1 => {
                v___x_4181_ = leanh::lean_unsigned_to_nat(1);
                v___x_4182_ = lean_nat_add(v_a_4177_, v___x_4181_);
                leanh::lean_dec(v_a_4177_);
                if v_isShared_4180_ == 0 {
                    leanh::lean_ctor_set(v___x_4179_, 1, v___x_4182_);
                    v___x_4184_ = v___x_4179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4176_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4182_);
                    v___x_4184_ = v_reuseFailAlloc_4185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4184_;
            }
            3 => {
                v___x_4191_ = leanh::lean_unsigned_to_nat(1);
                v___x_4192_ = lean_nat_add(v_a_4187_, v___x_4191_);
                leanh::lean_dec(v_a_4187_);
                if v_isShared_4190_ == 0 {
                    leanh::lean_ctor_set(v___x_4189_, 0, v___x_4192_);
                    v___x_4194_ = v___x_4189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
                    v___x_4194_ = v_reuseFailAlloc_4195_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_max(
    mut v_x_4199_: *mut leanh::LeanObject,
    mut v_x_4200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4200_) == 3 {
                    v_a_4201_ = leanh::lean_ctor_get(v_x_4200_, 0);
                    v_isSharedCheck_4209_ = (!leanh::lean_is_exclusive(v_x_4200_)) as u8;
                    if v_isSharedCheck_4209_ == 0 {
                        v___x_4203_ = v_x_4200_;
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4201_);
                        leanh::lean_dec(v_x_4200_);
                        v___x_4203_ = leanh::lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4210_ = leanh::lean_box(0);
                    v___x_4211_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4211_, 0, v_x_4200_);
                    leanh::lean_ctor_set(v___x_4211_, 1, v___x_4210_);
                    v___x_4212_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4212_, 0, v_x_4199_);
                    leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                    v___x_4213_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
                    return v___x_4213_;
                }
            }
            1 => {
                v___x_4205_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4205_, 0, v_x_4199_);
                leanh::lean_ctor_set(v___x_4205_, 1, v_a_4201_);
                if v_isShared_4204_ == 0 {
                    leanh::lean_ctor_set(v___x_4203_, 0, v___x_4205_);
                    v___x_4207_ = v___x_4203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
                    v___x_4207_ = v_reuseFailAlloc_4208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4207_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_imax(
    mut v_x_4214_: *mut leanh::LeanObject,
    mut v_x_4215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4215_) == 4 {
                    v_a_4216_ = leanh::lean_ctor_get(v_x_4215_, 0);
                    v_isSharedCheck_4224_ = (!leanh::lean_is_exclusive(v_x_4215_)) as u8;
                    if v_isSharedCheck_4224_ == 0 {
                        v___x_4218_ = v_x_4215_;
                        v_isShared_4219_ = v_isSharedCheck_4224_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4216_);
                        leanh::lean_dec(v_x_4215_);
                        v___x_4218_ = leanh::lean_box(0);
                        v_isShared_4219_ = v_isSharedCheck_4224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4225_ = leanh::lean_box(0);
                    v___x_4226_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4226_, 0, v_x_4215_);
                    leanh::lean_ctor_set(v___x_4226_, 1, v___x_4225_);
                    v___x_4227_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4227_, 0, v_x_4214_);
                    leanh::lean_ctor_set(v___x_4227_, 1, v___x_4226_);
                    v___x_4228_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4228_, 0, v___x_4227_);
                    return v___x_4228_;
                }
            }
            1 => {
                v___x_4220_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4220_, 0, v_x_4214_);
                leanh::lean_ctor_set(v___x_4220_, 1, v_a_4216_);
                if v_isShared_4219_ == 0 {
                    leanh::lean_ctor_set(v___x_4218_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
                    v___x_4222_ = v_reuseFailAlloc_4223_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4222_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_toResult(
    mut v_l_4247_: *mut leanh::LeanObject,
    mut v_a_4248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_4265_: u8 = 0;
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lIndex_x3f_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_l_4247_) {
                0 => {
                    v___x_4249_ = l_Lean_Level_PP_toResult___closed__0;
                    return v___x_4249_;
                }
                1 => {
                    v_a_4250_ = leanh::lean_ctor_get(v_l_4247_, 0);
                    leanh::lean_inc(v_a_4250_);
                    leanh::lean_dec_ref_known(v_l_4247_, 1);
                    v___x_4251_ = l_Lean_Level_PP_toResult(v_a_4250_, v_a_4248_);
                    v___x_4252_ = l_Lean_Level_PP_Result_succ(v___x_4251_);
                    return v___x_4252_;
                }
                2 => {
                    v_a_4253_ = leanh::lean_ctor_get(v_l_4247_, 0);
                    leanh::lean_inc(v_a_4253_);
                    v_a_4254_ = leanh::lean_ctor_get(v_l_4247_, 1);
                    leanh::lean_inc(v_a_4254_);
                    leanh::lean_dec_ref_known(v_l_4247_, 2);
                    v___x_4255_ = l_Lean_Level_PP_toResult(v_a_4253_, v_a_4248_);
                    v___x_4256_ = l_Lean_Level_PP_toResult(v_a_4254_, v_a_4248_);
                    v___x_4257_ = l_Lean_Level_PP_Result_max(v___x_4255_, v___x_4256_);
                    return v___x_4257_;
                }
                3 => {
                    v_a_4258_ = leanh::lean_ctor_get(v_l_4247_, 0);
                    leanh::lean_inc(v_a_4258_);
                    v_a_4259_ = leanh::lean_ctor_get(v_l_4247_, 1);
                    leanh::lean_inc(v_a_4259_);
                    leanh::lean_dec_ref_known(v_l_4247_, 2);
                    v___x_4260_ = l_Lean_Level_PP_toResult(v_a_4258_, v_a_4248_);
                    v___x_4261_ = l_Lean_Level_PP_toResult(v_a_4259_, v_a_4248_);
                    v___x_4262_ = l_Lean_Level_PP_Result_imax(v___x_4260_, v___x_4261_);
                    return v___x_4262_;
                }
                4 => {
                    v_a_4263_ = leanh::lean_ctor_get(v_l_4247_, 0);
                    leanh::lean_inc(v_a_4263_);
                    leanh::lean_dec_ref_known(v_l_4247_, 1);
                    v___x_4264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4264_, 0, v_a_4263_);
                    return v___x_4264_;
                }
                _ => {
                    v_mvars_4265_ = leanh::lean_ctor_get_uint8(
                        v_a_4248_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_mvars_4265_ == 0 {
                        leanh::lean_dec_ref_known(v_l_4247_, 1);
                        v___x_4266_ = l_Lean_Level_PP_toResult___closed__3;
                        return v___x_4266_;
                    } else {
                        v_a_4267_ = leanh::lean_ctor_get(v_l_4247_, 0);
                        leanh::lean_inc_n(v_a_4267_, 2);
                        leanh::lean_dec_ref_known(v_l_4247_, 1);
                        v_lIndex_x3f_4268_ = leanh::lean_ctor_get(v_a_4248_, 0);
                        leanh::lean_inc_ref(v_lIndex_x3f_4268_);
                        v___x_4269_ = leanh::lean_apply_1(v_lIndex_x3f_4268_, v_a_4267_);
                        if leanh::lean_obj_tag(v___x_4269_) == 1 {
                            leanh::lean_dec(v_a_4267_);
                            v_val_4270_ = leanh::lean_ctor_get(v___x_4269_, 0);
                            v_isSharedCheck_4281_ =
                                (!leanh::lean_is_exclusive(v___x_4269_)) as u8;
                            if v_isSharedCheck_4281_ == 0 {
                                v___x_4272_ = v___x_4269_;
                                v_isShared_4273_ = v_isSharedCheck_4281_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_4270_);
                                leanh::lean_dec(v___x_4269_);
                                v___x_4272_ = leanh::lean_box(0);
                                v_isShared_4273_ = v_isSharedCheck_4281_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_4269_);
                            v___x_4282_ = l_Lean_Level_PP_toResult___closed__7;
                            v___x_4283_ = l_Lean_Level_PP_toResult___closed__9;
                            v___x_4284_ =
                                l_Lean_Name_replacePrefix(v_a_4267_, v___x_4282_, v___x_4283_);
                            v___x_4285_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4285_, 0, v___x_4284_);
                            return v___x_4285_;
                        }
                    }
                }
            },
            1 => {
                v___x_4274_ = l_Lean_Level_PP_toResult___closed__5;
                v___x_4275_ = leanh::lean_unsigned_to_nat(1);
                v___x_4276_ = lean_nat_add(v_val_4270_, v___x_4275_);
                leanh::lean_dec(v_val_4270_);
                v___x_4277_ = l_Lean_Name_num___override(v___x_4274_, v___x_4276_);
                if v_isShared_4273_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4272_, 0);
                    leanh::lean_ctor_set(v___x_4272_, 0, v___x_4277_);
                    v___x_4279_ = v___x_4272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
                    v___x_4279_ = v_reuseFailAlloc_4280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_toResult___boxed(
    mut v_l_4286_: *mut leanh::LeanObject,
    mut v_a_4287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4288_ = l_Lean_Level_PP_toResult(v_l_4286_, v_a_4287_);
    leanh::lean_dec_ref(v_a_4287_);
    return v_res_4288_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
    v___x_4291_ = lean_string_length(v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1),
        core::ptr::addr_of_mut!(
            l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once
        ),
        _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1,
    );
    v___x_4293_ = lean_nat_to_int(v___x_4292_);
    return v___x_4293_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(
    mut v_x_4298_: *mut leanh::LeanObject,
    mut v_x_4299_: u8,
) -> *mut leanh::LeanObject {
    if v_x_4299_ == 0 {
        let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4306_: u8 = 0;
        let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4300_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once
            ),
            _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2,
        );
        v___x_4301_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
        v___x_4302_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
        leanh::lean_ctor_set(v___x_4302_, 1, v_x_4298_);
        v___x_4303_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4;
        v___x_4304_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4304_, 0, v___x_4302_);
        leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
        v___x_4305_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4305_, 0, v___x_4300_);
        leanh::lean_ctor_set(v___x_4305_, 1, v___x_4304_);
        v___x_4306_ = 0;
        v___x_4307_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_4307_, 0, v___x_4305_);
        leanh::lean_ctor_set_uint8(
            v___x_4307_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_4306_,
        );
        return v___x_4307_;
    } else {
        return v_x_4298_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(
    mut v_x_4308_: *mut leanh::LeanObject,
    mut v_x_4309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_57__boxed_4310_: u8 = 0;
    let mut v_res_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_57__boxed_4310_ = (leanh::lean_unbox(v_x_4309_) as u8);
    v_res_4311_ =
        l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_4308_, v_x_57__boxed_4310_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Level_PP_Result_format(
    mut v_x_4321_: *mut leanh::LeanObject,
    mut v_x_4322_: u8,
) -> *mut leanh::LeanObject {
    let mut v_a_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut v_a_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_zero_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4348_: u8 = 0;
    let mut v_one_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_x27_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_a_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_4321_) {
                0 => {
                    v_a_4323_ = leanh::lean_ctor_get(v_x_4321_, 0);
                    v_isSharedCheck_4332_ = (!leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4332_ == 0 {
                        v___x_4325_ = v_x_4321_;
                        v_isShared_4326_ = v_isSharedCheck_4332_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4323_);
                        leanh::lean_dec(v_x_4321_);
                        v___x_4325_ = leanh::lean_box(0);
                        v_isShared_4326_ = v_isSharedCheck_4332_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4333_ = leanh::lean_ctor_get(v_x_4321_, 0);
                    v_isSharedCheck_4341_ = (!leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4341_ == 0 {
                        v___x_4335_ = v_x_4321_;
                        v_isShared_4336_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4333_);
                        leanh::lean_dec(v_x_4321_);
                        v___x_4335_ = leanh::lean_box(0);
                        v_isShared_4336_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_4342_ = leanh::lean_ctor_get(v_x_4321_, 0);
                    v_a_4343_ = leanh::lean_ctor_get(v_x_4321_, 1);
                    v_isSharedCheck_4362_ = (!leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4362_ == 0 {
                        v___x_4345_ = v_x_4321_;
                        v_isShared_4346_ = v_isSharedCheck_4362_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4343_);
                        leanh::lean_inc(v_a_4342_);
                        leanh::lean_dec(v_x_4321_);
                        v___x_4345_ = leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4362_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_a_4363_ = leanh::lean_ctor_get(v_x_4321_, 0);
                    leanh::lean_inc(v_a_4363_);
                    leanh::lean_dec_ref_known(v_x_4321_, 1);
                    v___x_4364_ = l_Lean_Level_PP_Result_format___closed__3;
                    v___x_4365_ =
                        l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_4363_);
                    v___x_4366_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4366_, 0, v___x_4364_);
                    leanh::lean_ctor_set(v___x_4366_, 1, v___x_4365_);
                    v___x_4367_ = 0;
                    v___x_4368_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_4368_, 0, v___x_4366_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4368_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4367_,
                    );
                    v___x_4369_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(
                        v___x_4368_,
                        v_x_4322_,
                    );
                    return v___x_4369_;
                }
                _ => {
                    v_a_4370_ = leanh::lean_ctor_get(v_x_4321_, 0);
                    leanh::lean_inc(v_a_4370_);
                    leanh::lean_dec_ref_known(v_x_4321_, 1);
                    v___x_4371_ = l_Lean_Level_PP_Result_format___closed__5;
                    v___x_4372_ =
                        l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_4370_);
                    v___x_4373_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4373_, 0, v___x_4371_);
                    leanh::lean_ctor_set(v___x_4373_, 1, v___x_4372_);
                    v___x_4374_ = 0;
                    v___x_4375_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    leanh::lean_ctor_set(v___x_4375_, 0, v___x_4373_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4375_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v___x_4374_,
                    );
                    v___x_4376_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(
                        v___x_4375_,
                        v_x_4322_,
                    );
                    return v___x_4376_;
                }
            },
            1 => {
                v___x_4327_ = 1;
                v___x_4328_ = l_Lean_Name_toString(v_a_4323_, v___x_4327_);
                if v_isShared_4326_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4325_, 3);
                    leanh::lean_ctor_set(v___x_4325_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
                    v___x_4330_ = v_reuseFailAlloc_4331_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4330_;
            }
            3 => {
                v___x_4337_ = l_Nat_reprFast(v_a_4333_);
                if v_isShared_4336_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4335_, 3);
                    leanh::lean_ctor_set(v___x_4335_, 0, v___x_4337_);
                    v___x_4339_ = v___x_4335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4339_;
            }
            5 => {
                v_zero_4347_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4348_ = lean_nat_dec_eq(v_a_4343_, v_zero_4347_);
                if v_isZero_4348_ == 1 {
                    leanh::lean_del_object(v___x_4345_);
                    leanh::lean_dec(v_a_4343_);
                    v_x_4321_ = v_a_4342_;
                    state = 0;
                    continue;
                } else {
                    v_one_4350_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4351_ = lean_nat_sub(v_a_4343_, v_one_4350_);
                    leanh::lean_dec(v_a_4343_);
                    v_f_x27_4352_ = l_Lean_Level_PP_Result_format(v_a_4342_, v_isZero_4348_);
                    v___x_4353_ = l_Lean_Level_PP_Result_format___closed__1;
                    if v_isShared_4346_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4345_, 5);
                        leanh::lean_ctor_set(v___x_4345_, 1, v___x_4353_);
                        leanh::lean_ctor_set(v___x_4345_, 0, v_f_x27_4352_);
                        v___x_4355_ = v___x_4345_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_f_x27_4352_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___x_4353_);
                        v___x_4355_ = v_reuseFailAlloc_4361_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4356_ = lean_nat_add(v_n_4351_, v_one_4350_);
                leanh::lean_dec(v_n_4351_);
                v___x_4357_ = l_Nat_reprFast(v___x_4356_);
                v___x_4358_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4358_, 0, v___x_4357_);
                v___x_4359_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4359_, 0, v___x_4355_);
                leanh::lean_ctor_set(v___x_4359_, 1, v___x_4358_);
                v___x_4360_ =
                    l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_4359_, v_x_4322_);
                return v___x_4360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(
    mut v_x_4377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4377_) == 0 {
                    v___x_4378_ = leanh::lean_box(0);
                    return v___x_4378_;
                } else {
                    v_head_4379_ = leanh::lean_ctor_get(v_x_4377_, 0);
                    v_tail_4380_ = leanh::lean_ctor_get(v_x_4377_, 1);
                    v_isSharedCheck_4392_ = (!leanh::lean_is_exclusive(v_x_4377_)) as u8;
                    if v_isSharedCheck_4392_ == 0 {
                        v___x_4382_ = v_x_4377_;
                        v_isShared_4383_ = v_isSharedCheck_4392_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4380_);
                        leanh::lean_inc(v_head_4379_);
                        leanh::lean_dec(v_x_4377_);
                        v___x_4382_ = leanh::lean_box(0);
                        v_isShared_4383_ = v_isSharedCheck_4392_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4384_ = leanh::lean_box(1);
                v___x_4385_ = 0;
                v___x_4386_ = l_Lean_Level_PP_Result_format(v_head_4379_, v___x_4385_);
                if v_isShared_4383_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4382_, 5);
                    leanh::lean_ctor_set(v___x_4382_, 1, v___x_4386_);
                    leanh::lean_ctor_set(v___x_4382_, 0, v___x_4384_);
                    v___x_4388_ = v___x_4382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 1, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4389_ =
                    l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_4380_);
                v___x_4390_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4390_, 0, v___x_4388_);
                leanh::lean_ctor_set(v___x_4390_, 1, v___x_4389_);
                return v___x_4390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_format___boxed(
    mut v_x_4393_: *mut leanh::LeanObject,
    mut v_x_4394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_270__boxed_4395_: u8 = 0;
    let mut v_res_4396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_270__boxed_4395_ = (leanh::lean_unbox(v_x_4394_) as u8);
    v_res_4396_ = l_Lean_Level_PP_Result_format(v_x_4393_, v_x_270__boxed_4395_);
    return v_res_4396_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = 0;
    v___x_4398_ = leanh::lean_box(0);
    v___x_4399_ = l_Lean_SourceInfo_fromRef(v___x_4398_, v___x_4397_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4409_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
    v___x_4410_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4411_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4411_, 0, v___x_4410_);
    leanh::lean_ctor_set(v___x_4411_, 1, v___x_4409_);
    return v___x_4411_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__7() -> *mut leanh::LeanObject {
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4412_ = l_Lean_instReprData___lam__0___closed__0;
    v___x_4413_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4414_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4414_, 0, v___x_4413_);
    leanh::lean_ctor_set(v___x_4414_, 1, v___x_4412_);
    return v___x_4414_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__12() -> *mut leanh::LeanObject {
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4427_ = l_Lean_Level_PP_Result_format___closed__2;
    v___x_4428_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4429_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4429_, 0, v___x_4428_);
    leanh::lean_ctor_set(v___x_4429_, 1, v___x_4427_);
    return v___x_4429_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__15() -> *mut leanh::LeanObject {
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4433_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_4433_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_Lean_Level_PP_Result_format___closed__4;
    v___x_4440_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4441_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4441_, 0, v___x_4440_);
    leanh::lean_ctor_set(v___x_4441_, 1, v___x_4439_);
    return v___x_4441_;
}
pub unsafe fn l_Lean_Level_PP_Result_quote(
    mut v_r_4442_: *mut leanh::LeanObject,
    mut v_prec_4443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v_zero_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4465_: u8 = 0;
    let mut v_one_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_a_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4504_: usize = 0;
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_r_4442_) {
                0 => {
                    v_a_4453_ = leanh::lean_ctor_get(v_r_4442_, 0);
                    leanh::lean_inc(v_a_4453_);
                    leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4454_ = lean_mk_syntax_ident(v_a_4453_);
                    return v___x_4454_;
                }
                1 => {
                    v_a_4455_ = leanh::lean_ctor_get(v_r_4442_, 0);
                    leanh::lean_inc(v_a_4455_);
                    leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4456_ = l_Nat_reprFast(v_a_4455_);
                    v___x_4457_ = leanh::lean_box(2);
                    v___x_4458_ = l_Lean_Syntax_mkNumLit(v___x_4456_, v___x_4457_);
                    return v___x_4458_;
                }
                2 => {
                    v_a_4459_ = leanh::lean_ctor_get(v_r_4442_, 0);
                    v_a_4460_ = leanh::lean_ctor_get(v_r_4442_, 1);
                    v_isSharedCheck_4483_ = (!leanh::lean_is_exclusive(v_r_4442_)) as u8;
                    if v_isSharedCheck_4483_ == 0 {
                        v___x_4462_ = v_r_4442_;
                        v_isShared_4463_ = v_isSharedCheck_4483_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4460_);
                        leanh::lean_inc(v_a_4459_);
                        leanh::lean_dec(v_r_4442_);
                        v___x_4462_ = leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4483_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    v_a_4484_ = leanh::lean_ctor_get(v_r_4442_, 0);
                    leanh::lean_inc(v_a_4484_);
                    leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4485_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4486_ = l_Lean_Level_PP_Result_quote___closed__11;
                    v___x_4487_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__12_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__12,
                    );
                    v___x_4488_ = l_Lean_Level_PP_Result_quote___closed__14;
                    v___x_4489_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__15,
                    );
                    v___x_4490_ = lean_array_mk(v_a_4484_);
                    v_sz_4491_ = lean_array_size(v___x_4490_);
                    v___x_4492_ = 0usize;
                    v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_4491_, v___x_4492_, v___x_4490_);
                    v___x_4494_ = l_Array_append___redArg(v___x_4489_, v___x_4493_);
                    leanh::lean_dec_ref(v___x_4493_);
                    v___x_4495_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4495_, 0, v___x_4485_);
                    leanh::lean_ctor_set(v___x_4495_, 1, v___x_4488_);
                    leanh::lean_ctor_set(v___x_4495_, 2, v___x_4494_);
                    v___x_4496_ =
                        l_Lean_Syntax_node2(v___x_4485_, v___x_4486_, v___x_4487_, v___x_4495_);
                    v_s_4445_ = v___x_4496_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_a_4497_ = leanh::lean_ctor_get(v_r_4442_, 0);
                    leanh::lean_inc(v_a_4497_);
                    leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4498_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4499_ = l_Lean_Level_PP_Result_quote___closed__16;
                    v___x_4500_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__17),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__17_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__17,
                    );
                    v___x_4501_ = l_Lean_Level_PP_Result_quote___closed__14;
                    v___x_4502_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__15,
                    );
                    v___x_4503_ = lean_array_mk(v_a_4497_);
                    v_sz_4504_ = lean_array_size(v___x_4503_);
                    v___x_4505_ = 0usize;
                    v___x_4506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_4504_, v___x_4505_, v___x_4503_);
                    v___x_4507_ = l_Array_append___redArg(v___x_4502_, v___x_4506_);
                    leanh::lean_dec_ref(v___x_4506_);
                    v___x_4508_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_4508_, 0, v___x_4498_);
                    leanh::lean_ctor_set(v___x_4508_, 1, v___x_4501_);
                    leanh::lean_ctor_set(v___x_4508_, 2, v___x_4507_);
                    v___x_4509_ =
                        l_Lean_Syntax_node2(v___x_4498_, v___x_4499_, v___x_4500_, v___x_4508_);
                    v_s_4445_ = v___x_4509_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4446_ = leanh::lean_unsigned_to_nat(0);
                v___x_4447_ = lean_nat_dec_lt(v___x_4446_, v_prec_4443_);
                if v___x_4447_ == 0 {
                    return v_s_4445_;
                } else {
                    v___x_4448_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4449_ = l_Lean_Level_PP_Result_quote___closed__5;
                    v___x_4450_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__6_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__6,
                    );
                    v___x_4451_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__7_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__7,
                    );
                    v___x_4452_ = l_Lean_Syntax_node3(
                        v___x_4448_,
                        v___x_4449_,
                        v___x_4450_,
                        v_s_4445_,
                        v___x_4451_,
                    );
                    return v___x_4452_;
                }
            }
            2 => {
                v_zero_4464_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_4465_ = lean_nat_dec_eq(v_a_4460_, v_zero_4464_);
                if v_isZero_4465_ == 1 {
                    leanh::lean_del_object(v___x_4462_);
                    leanh::lean_dec(v_a_4460_);
                    v_r_4442_ = v_a_4459_;
                    state = 0;
                    continue;
                } else {
                    v_one_4467_ = leanh::lean_unsigned_to_nat(1);
                    v_n_4468_ = lean_nat_sub(v_a_4460_, v_one_4467_);
                    leanh::lean_dec(v_a_4460_);
                    v___x_4469_ = leanh::lean_box(0);
                    v___x_4470_ = l_Lean_SourceInfo_fromRef(v___x_4469_, v_isZero_4465_);
                    v___x_4471_ = l_Lean_Level_PP_Result_quote___closed__9;
                    v___x_4472_ = leanh::lean_unsigned_to_nat(65);
                    v___x_4473_ = l_Lean_Level_PP_Result_quote(v_a_4459_, v___x_4472_);
                    v___x_4474_ = l_Lean_Level_PP_Result_quote___closed__10;
                    leanh::lean_inc(v___x_4470_);
                    if v_isShared_4463_ == 0 {
                        leanh::lean_ctor_set(v___x_4462_, 1, v___x_4474_);
                        leanh::lean_ctor_set(v___x_4462_, 0, v___x_4470_);
                        v___x_4476_ = v___x_4462_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4482_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4470_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4474_);
                        v___x_4476_ = v_reuseFailAlloc_4482_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4477_ = lean_nat_add(v_n_4468_, v_one_4467_);
                leanh::lean_dec(v_n_4468_);
                v___x_4478_ = l_Nat_reprFast(v___x_4477_);
                v___x_4479_ = leanh::lean_box(2);
                v___x_4480_ = l_Lean_Syntax_mkNumLit(v___x_4478_, v___x_4479_);
                v___x_4481_ = l_Lean_Syntax_node3(
                    v___x_4470_,
                    v___x_4471_,
                    v___x_4473_,
                    v___x_4476_,
                    v___x_4480_,
                );
                v_s_4445_ = v___x_4481_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(
    mut v_sz_4510_: usize,
    mut v_i_4511_: usize,
    mut v_bs_4512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4513_: u8 = 0;
    let mut v_v_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: usize = 0;
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4513_ = lean_usize_dec_lt(v_i_4511_, v_sz_4510_);
                if v___x_4513_ == 0 {
                    return v_bs_4512_;
                } else {
                    v_v_4514_ = lean_array_uget(v_bs_4512_, v_i_4511_);
                    v___x_4515_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4516_ = lean_array_uset(v_bs_4512_, v_i_4511_, v___x_4515_);
                    v___x_4517_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4518_ = l_Lean_Level_PP_Result_quote(v_v_4514_, v___x_4517_);
                    v___x_4519_ = 1usize;
                    v___x_4520_ = lean_usize_add(v_i_4511_, v___x_4519_);
                    v___x_4521_ = lean_array_uset(v_bs_x27_4516_, v_i_4511_, v___x_4518_);
                    v_i_4511_ = v___x_4520_;
                    v_bs_4512_ = v___x_4521_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0___boxed(
    mut v_sz_4523_: *mut leanh::LeanObject,
    mut v_i_4524_: *mut leanh::LeanObject,
    mut v_bs_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4526_: usize = 0;
    let mut v_i_boxed_4527_: usize = 0;
    let mut v_res_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4526_ = leanh::lean_unbox_usize(v_sz_4523_);
    leanh::lean_dec(v_sz_4523_);
    v_i_boxed_4527_ = leanh::lean_unbox_usize(v_i_4524_);
    leanh::lean_dec(v_i_4524_);
    v_res_4528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_4526_, v_i_boxed_4527_, v_bs_4525_);
    return v_res_4528_;
}
pub unsafe fn l_Lean_Level_PP_Result_quote___boxed(
    mut v_r_4529_: *mut leanh::LeanObject,
    mut v_prec_4530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ = l_Lean_Level_PP_Result_quote(v_r_4529_, v_prec_4530_);
    leanh::lean_dec(v_prec_4530_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_Level_format(
    mut v_u_4532_: *mut leanh::LeanObject,
    mut v_mvars_4533_: u8,
    mut v_lIndex_x3f_4534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: u8 = 0;
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_4535_, 0, v_lIndex_x3f_4534_);
    leanh::lean_ctor_set_uint8(
        v___x_4535_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_mvars_4533_,
    );
    v___x_4536_ = l_Lean_Level_PP_toResult(v_u_4532_, v___x_4535_);
    leanh::lean_dec_ref_known(v___x_4535_, 1);
    v___x_4537_ = 1;
    v___x_4538_ = l_Lean_Level_PP_Result_format(v___x_4536_, v___x_4537_);
    return v___x_4538_;
}
pub unsafe fn l_Lean_Level_format___boxed(
    mut v_u_4539_: *mut leanh::LeanObject,
    mut v_mvars_4540_: *mut leanh::LeanObject,
    mut v_lIndex_x3f_4541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvars_boxed_4542_: u8 = 0;
    let mut v_res_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mvars_boxed_4542_ = (leanh::lean_unbox(v_mvars_4540_) as u8);
    v_res_4543_ = l_Lean_Level_format(v_u_4539_, v_mvars_boxed_4542_, v_lIndex_x3f_4541_);
    return v_res_4543_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__0(
    mut v_x_4544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = leanh::lean_box(0);
    return v___x_4545_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__0___boxed(
    mut v_x_4546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4547_ = l_Lean_Level_instToFormat___lam__0(v_x_4546_);
    leanh::lean_dec(v_x_4546_);
    return v_res_4547_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__1(
    mut v___f_4548_: *mut leanh::LeanObject,
    mut v_u_4549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = 1;
    v___x_4551_ = l_Lean_Level_format(v_u_4549_, v___x_4550_, v___f_4548_);
    return v___x_4551_;
}
pub unsafe fn l_Lean_Level_instToString___lam__1(
    mut v___f_4556_: *mut leanh::LeanObject,
    mut v_u_4557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = 1;
    v___x_4559_ = l_Lean_Level_format(v_u_4557_, v___x_4558_, v___f_4556_);
    v___x_4560_ = l_Std_Format_defWidth;
    v___x_4561_ = leanh::lean_unsigned_to_nat(0);
    v___x_4562_ = l_Std_Format_pretty(v___x_4559_, v___x_4560_, v___x_4561_, v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l_Lean_Level_quote(
    mut v_u_4566_: *mut leanh::LeanObject,
    mut v_prec_4567_: *mut leanh::LeanObject,
    mut v_mvars_4568_: u8,
    mut v_lIndex_x3f_4569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_4570_, 0, v_lIndex_x3f_4569_);
    leanh::lean_ctor_set_uint8(
        v___x_4570_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v_mvars_4568_,
    );
    v___x_4571_ = l_Lean_Level_PP_toResult(v_u_4566_, v___x_4570_);
    leanh::lean_dec_ref_known(v___x_4570_, 1);
    v___x_4572_ = l_Lean_Level_PP_Result_quote(v___x_4571_, v_prec_4567_);
    return v___x_4572_;
}
pub unsafe fn l_Lean_Level_quote___boxed(
    mut v_u_4573_: *mut leanh::LeanObject,
    mut v_prec_4574_: *mut leanh::LeanObject,
    mut v_mvars_4575_: *mut leanh::LeanObject,
    mut v_lIndex_x3f_4576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvars_boxed_4577_: u8 = 0;
    let mut v_res_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_mvars_boxed_4577_ = (leanh::lean_unbox(v_mvars_4575_) as u8);
    v_res_4578_ = l_Lean_Level_quote(
        v_u_4573_,
        v_prec_4574_,
        v_mvars_boxed_4577_,
        v_lIndex_x3f_4576_,
    );
    leanh::lean_dec(v_prec_4574_);
    return v_res_4578_;
}
pub unsafe fn l_Lean_Level_instQuoteMkStr1___lam__1(
    mut v___f_4579_: *mut leanh::LeanObject,
    mut v_u_4580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4581_ = leanh::lean_unsigned_to_nat(0);
    v___x_4582_ = 1;
    v___x_4583_ = l_Lean_Level_quote(v_u_4580_, v___x_4581_, v___x_4582_, v___f_4579_);
    return v___x_4583_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(
    mut v_u_4587_: *mut leanh::LeanObject,
    mut v_v_4588_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4590_: u8 = 0;
    let mut v___x_4591_: u8 = 0;
    let mut v_a_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4596_ = l_Lean_Level_isExplicit(v_v_4588_);
                if v___x_4596_ == 0 {
                    v___y_4590_ = v___x_4596_;
                    state = 1;
                    continue;
                } else {
                    v___x_4597_ = l_Lean_Level_getOffset(v_v_4588_);
                    v___x_4598_ = l_Lean_Level_getOffset(v_u_4587_);
                    v___x_4599_ = lean_nat_dec_le(v___x_4597_, v___x_4598_);
                    leanh::lean_dec(v___x_4598_);
                    leanh::lean_dec(v___x_4597_);
                    v___y_4590_ = v___x_4599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4591_ = 1;
                if v___y_4590_ == 0 {
                    if leanh::lean_obj_tag(v_u_4587_) == 2 {
                        v_a_4592_ = leanh::lean_ctor_get(v_u_4587_, 0);
                        v_a_4593_ = leanh::lean_ctor_get(v_u_4587_, 1);
                        v___x_4594_ = lean_level_eq(v_v_4588_, v_a_4592_);
                        if v___x_4594_ == 0 {
                            v___x_4595_ = lean_level_eq(v_v_4588_, v_a_4593_);
                            return v___x_4595_;
                        } else {
                            return v___x_4591_;
                        }
                    } else {
                        return v___y_4590_;
                    }
                } else {
                    return v___x_4591_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0___boxed(
    mut v_u_4600_: *mut leanh::LeanObject,
    mut v_v_4601_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4602_: u8 = 0;
    let mut v_r_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4602_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_4600_, v_v_4601_);
    leanh::lean_dec(v_v_4601_);
    leanh::lean_dec(v_u_4600_);
    v_r_4603_ = leanh::lean_box((v_res_4602_) as usize);
    return v_r_4603_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore(
    mut v_u_4604_: *mut leanh::LeanObject,
    mut v_v_4605_: *mut leanh::LeanObject,
    mut v_elseK_4606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4607_: u8 = 0;
    v___x_4607_ = lean_level_eq(v_u_4604_, v_v_4605_);
    if v___x_4607_ == 0 {
        let mut v___x_4608_: u8 = 0;
        v___x_4608_ = l_Lean_Level_isZero(v_u_4604_);
        if v___x_4608_ == 0 {
            let mut v___x_4609_: u8 = 0;
            v___x_4609_ = l_Lean_Level_isZero(v_v_4605_);
            if v___x_4609_ == 0 {
                let mut v___x_4610_: u8 = 0;
                v___x_4610_ =
                    l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_4604_, v_v_4605_);
                if v___x_4610_ == 0 {
                    let mut v___x_4611_: u8 = 0;
                    v___x_4611_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(
                        v_v_4605_, v_u_4604_,
                    );
                    if v___x_4611_ == 0 {
                        let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4614_: u8 = 0;
                        v___x_4612_ = l_Lean_Level_getLevelOffset(v_u_4604_);
                        v___x_4613_ = l_Lean_Level_getLevelOffset(v_v_4605_);
                        v___x_4614_ = lean_level_eq(v___x_4612_, v___x_4613_);
                        leanh::lean_dec(v___x_4613_);
                        leanh::lean_dec(v___x_4612_);
                        if v___x_4614_ == 0 {
                            let mut v___x_4615_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4616_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_4615_ = leanh::lean_box(0);
                            v___x_4616_ = leanh::lean_apply_1(v_elseK_4606_, v___x_4615_);
                            return v___x_4616_;
                        } else {
                            let mut v___x_4617_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4618_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4619_: u8 = 0;
                            leanh::lean_dec_ref(v_elseK_4606_);
                            v___x_4617_ = l_Lean_Level_getOffset(v_v_4605_);
                            v___x_4618_ = l_Lean_Level_getOffset(v_u_4604_);
                            v___x_4619_ = lean_nat_dec_le(v___x_4617_, v___x_4618_);
                            leanh::lean_dec(v___x_4618_);
                            leanh::lean_dec(v___x_4617_);
                            if v___x_4619_ == 0 {
                                leanh::lean_inc(v_v_4605_);
                                return v_v_4605_;
                            } else {
                                leanh::lean_inc(v_u_4604_);
                                return v_u_4604_;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_elseK_4606_);
                        leanh::lean_inc(v_v_4605_);
                        return v_v_4605_;
                    }
                } else {
                    leanh::lean_dec_ref(v_elseK_4606_);
                    leanh::lean_inc(v_u_4604_);
                    return v_u_4604_;
                }
            } else {
                leanh::lean_dec_ref(v_elseK_4606_);
                leanh::lean_inc(v_u_4604_);
                return v_u_4604_;
            }
        } else {
            leanh::lean_dec_ref(v_elseK_4606_);
            leanh::lean_inc(v_v_4605_);
            return v_v_4605_;
        }
    } else {
        leanh::lean_dec_ref(v_elseK_4606_);
        leanh::lean_inc(v_u_4604_);
        return v_u_4604_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(
    mut v_u_4620_: *mut leanh::LeanObject,
    mut v_v_4621_: *mut leanh::LeanObject,
    mut v_elseK_4622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_4620_, v_v_4621_, v_elseK_4622_);
    leanh::lean_dec(v_v_4621_);
    leanh::lean_dec(v_u_4620_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_mkLevelMax_x27(
    mut v_u_4624_: *mut leanh::LeanObject,
    mut v_v_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4626_: u8 = 0;
    v___x_4626_ = lean_level_eq(v_u_4624_, v_v_4625_);
    if v___x_4626_ == 0 {
        let mut v___x_4627_: u8 = 0;
        v___x_4627_ = l_Lean_Level_isZero(v_u_4624_);
        if v___x_4627_ == 0 {
            let mut v___x_4628_: u8 = 0;
            v___x_4628_ = l_Lean_Level_isZero(v_v_4625_);
            if v___x_4628_ == 0 {
                let mut v___x_4629_: u8 = 0;
                v___x_4629_ =
                    l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_4624_, v_v_4625_);
                if v___x_4629_ == 0 {
                    let mut v___x_4630_: u8 = 0;
                    v___x_4630_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(
                        v_v_4625_, v_u_4624_,
                    );
                    if v___x_4630_ == 0 {
                        let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4633_: u8 = 0;
                        v___x_4631_ = l_Lean_Level_getLevelOffset(v_u_4624_);
                        v___x_4632_ = l_Lean_Level_getLevelOffset(v_v_4625_);
                        v___x_4633_ = lean_level_eq(v___x_4631_, v___x_4632_);
                        leanh::lean_dec(v___x_4632_);
                        leanh::lean_dec(v___x_4631_);
                        if v___x_4633_ == 0 {
                            let mut v___x_4634_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_4634_ = l_Lean_Level_max___override(v_u_4624_, v_v_4625_);
                            return v___x_4634_;
                        } else {
                            let mut v___x_4635_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4636_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4637_: u8 = 0;
                            v___x_4635_ = l_Lean_Level_getOffset(v_v_4625_);
                            v___x_4636_ = l_Lean_Level_getOffset(v_u_4624_);
                            v___x_4637_ = lean_nat_dec_le(v___x_4635_, v___x_4636_);
                            leanh::lean_dec(v___x_4636_);
                            leanh::lean_dec(v___x_4635_);
                            if v___x_4637_ == 0 {
                                leanh::lean_dec(v_u_4624_);
                                return v_v_4625_;
                            } else {
                                leanh::lean_dec(v_v_4625_);
                                return v_u_4624_;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_u_4624_);
                        return v_v_4625_;
                    }
                } else {
                    leanh::lean_dec(v_v_4625_);
                    return v_u_4624_;
                }
            } else {
                leanh::lean_dec(v_v_4625_);
                return v_u_4624_;
            }
        } else {
            leanh::lean_dec(v_u_4624_);
            return v_v_4625_;
        }
    } else {
        leanh::lean_dec(v_v_4625_);
        return v_u_4624_;
    }
}
pub unsafe fn l_Lean_simpLevelMax_x27(
    mut v_u_4638_: *mut leanh::LeanObject,
    mut v_v_4639_: *mut leanh::LeanObject,
    mut v_d_4640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4641_: u8 = 0;
    v___x_4641_ = lean_level_eq(v_u_4638_, v_v_4639_);
    if v___x_4641_ == 0 {
        let mut v___x_4642_: u8 = 0;
        v___x_4642_ = l_Lean_Level_isZero(v_u_4638_);
        if v___x_4642_ == 0 {
            let mut v___x_4643_: u8 = 0;
            v___x_4643_ = l_Lean_Level_isZero(v_v_4639_);
            if v___x_4643_ == 0 {
                let mut v___x_4644_: u8 = 0;
                v___x_4644_ =
                    l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_4638_, v_v_4639_);
                if v___x_4644_ == 0 {
                    let mut v___x_4645_: u8 = 0;
                    v___x_4645_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(
                        v_v_4639_, v_u_4638_,
                    );
                    if v___x_4645_ == 0 {
                        let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4648_: u8 = 0;
                        v___x_4646_ = l_Lean_Level_getLevelOffset(v_u_4638_);
                        v___x_4647_ = l_Lean_Level_getLevelOffset(v_v_4639_);
                        v___x_4648_ = lean_level_eq(v___x_4646_, v___x_4647_);
                        leanh::lean_dec(v___x_4647_);
                        leanh::lean_dec(v___x_4646_);
                        if v___x_4648_ == 0 {
                            leanh::lean_inc(v_d_4640_);
                            return v_d_4640_;
                        } else {
                            let mut v___x_4649_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4650_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4651_: u8 = 0;
                            v___x_4649_ = l_Lean_Level_getOffset(v_v_4639_);
                            v___x_4650_ = l_Lean_Level_getOffset(v_u_4638_);
                            v___x_4651_ = lean_nat_dec_le(v___x_4649_, v___x_4650_);
                            leanh::lean_dec(v___x_4650_);
                            leanh::lean_dec(v___x_4649_);
                            if v___x_4651_ == 0 {
                                leanh::lean_inc(v_v_4639_);
                                return v_v_4639_;
                            } else {
                                leanh::lean_inc(v_u_4638_);
                                return v_u_4638_;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_v_4639_);
                        return v_v_4639_;
                    }
                } else {
                    leanh::lean_inc(v_u_4638_);
                    return v_u_4638_;
                }
            } else {
                leanh::lean_inc(v_u_4638_);
                return v_u_4638_;
            }
        } else {
            leanh::lean_inc(v_v_4639_);
            return v_v_4639_;
        }
    } else {
        leanh::lean_inc(v_u_4638_);
        return v_u_4638_;
    }
}
pub unsafe fn l_Lean_simpLevelMax_x27___boxed(
    mut v_u_4652_: *mut leanh::LeanObject,
    mut v_v_4653_: *mut leanh::LeanObject,
    mut v_d_4654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_simpLevelMax_x27(v_u_4652_, v_v_4653_, v_d_4654_);
    leanh::lean_dec(v_d_4654_);
    leanh::lean_dec(v_v_4653_);
    leanh::lean_dec(v_u_4652_);
    return v_res_4655_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelIMaxCore(
    mut v_u_4656_: *mut leanh::LeanObject,
    mut v_v_4657_: *mut leanh::LeanObject,
    mut v_elseK_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4659_: u8 = 0;
    v___x_4659_ = l_Lean_Level_isNeverZero(v_v_4657_);
    if v___x_4659_ == 0 {
        let mut v___x_4660_: u8 = 0;
        v___x_4660_ = l_Lean_Level_isZero(v_v_4657_);
        if v___x_4660_ == 0 {
            let mut v___x_4661_: u8 = 0;
            v___x_4661_ = l_Lean_Level_isZero(v_u_4656_);
            if v___x_4661_ == 0 {
                let mut v___x_4662_: u8 = 0;
                v___x_4662_ = lean_level_eq(v_u_4656_, v_v_4657_);
                leanh::lean_dec(v_v_4657_);
                if v___x_4662_ == 0 {
                    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_u_4656_);
                    v___x_4663_ = leanh::lean_box(0);
                    v___x_4664_ = leanh::lean_apply_1(v_elseK_4658_, v___x_4663_);
                    return v___x_4664_;
                } else {
                    leanh::lean_dec_ref(v_elseK_4658_);
                    return v_u_4656_;
                }
            } else {
                leanh::lean_dec_ref(v_elseK_4658_);
                leanh::lean_dec(v_u_4656_);
                return v_v_4657_;
            }
        } else {
            leanh::lean_dec_ref(v_elseK_4658_);
            leanh::lean_dec(v_u_4656_);
            return v_v_4657_;
        }
    } else {
        let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_elseK_4658_);
        v___x_4665_ = l_Lean_mkLevelMax_x27(v_u_4656_, v_v_4657_);
        return v___x_4665_;
    }
}
pub unsafe fn l_Lean_mkLevelIMax_x27(
    mut v_u_4666_: *mut leanh::LeanObject,
    mut v_v_4667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4668_: u8 = 0;
    v___x_4668_ = l_Lean_Level_isNeverZero(v_v_4667_);
    if v___x_4668_ == 0 {
        let mut v___x_4669_: u8 = 0;
        v___x_4669_ = l_Lean_Level_isZero(v_v_4667_);
        if v___x_4669_ == 0 {
            let mut v___x_4670_: u8 = 0;
            v___x_4670_ = l_Lean_Level_isZero(v_u_4666_);
            if v___x_4670_ == 0 {
                let mut v___x_4671_: u8 = 0;
                v___x_4671_ = lean_level_eq(v_u_4666_, v_v_4667_);
                if v___x_4671_ == 0 {
                    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_4672_ = l_Lean_Level_imax___override(v_u_4666_, v_v_4667_);
                    return v___x_4672_;
                } else {
                    leanh::lean_dec(v_v_4667_);
                    return v_u_4666_;
                }
            } else {
                leanh::lean_dec(v_u_4666_);
                return v_v_4667_;
            }
        } else {
            leanh::lean_dec(v_u_4666_);
            return v_v_4667_;
        }
    } else {
        let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4673_ = l_Lean_mkLevelMax_x27(v_u_4666_, v_v_4667_);
        return v___x_4673_;
    }
}
pub unsafe fn l_Lean_simpLevelIMax_x27(
    mut v_u_4674_: *mut leanh::LeanObject,
    mut v_v_4675_: *mut leanh::LeanObject,
    mut v_d_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4677_: u8 = 0;
    v___x_4677_ = l_Lean_Level_isNeverZero(v_v_4675_);
    if v___x_4677_ == 0 {
        let mut v___x_4678_: u8 = 0;
        v___x_4678_ = l_Lean_Level_isZero(v_v_4675_);
        if v___x_4678_ == 0 {
            let mut v___x_4679_: u8 = 0;
            v___x_4679_ = l_Lean_Level_isZero(v_u_4674_);
            if v___x_4679_ == 0 {
                let mut v___x_4680_: u8 = 0;
                v___x_4680_ = lean_level_eq(v_u_4674_, v_v_4675_);
                leanh::lean_dec(v_v_4675_);
                if v___x_4680_ == 0 {
                    leanh::lean_dec(v_u_4674_);
                    leanh::lean_inc(v_d_4676_);
                    return v_d_4676_;
                } else {
                    return v_u_4674_;
                }
            } else {
                leanh::lean_dec(v_u_4674_);
                return v_v_4675_;
            }
        } else {
            leanh::lean_dec(v_u_4674_);
            return v_v_4675_;
        }
    } else {
        let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4681_ = l_Lean_mkLevelMax_x27(v_u_4674_, v_v_4675_);
        return v___x_4681_;
    }
}
pub unsafe fn l_Lean_simpLevelIMax_x27___boxed(
    mut v_u_4682_: *mut leanh::LeanObject,
    mut v_v_4683_: *mut leanh::LeanObject,
    mut v_d_4684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4685_ = l_Lean_simpLevelIMax_x27(v_u_4682_, v_v_4683_, v_d_4684_);
    leanh::lean_dec(v_d_4684_);
    return v_res_4685_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
    v___x_4689_ = leanh::lean_unsigned_to_nat(14);
    v___x_4690_ = leanh::lean_unsigned_to_nat(564);
    v___x_4691_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0;
    v___x_4692_ = l_Lean_Level_mvarId_x21___closed__0;
    v___x_4693_ = l_mkPanicMessageWithDecl(
        v___x_4692_,
        v___x_4691_,
        v___x_4690_,
        v___x_4689_,
        v___x_4688_,
    );
    return v___x_4693_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(
    mut v_lvl_4694_: *mut leanh::LeanObject,
    mut v_newLvl_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_lvl_4694_) == 1 {
        let mut v_a_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4697_: usize = 0;
        let mut v___x_4698_: usize = 0;
        let mut v___x_4699_: u8 = 0;
        v_a_4696_ = leanh::lean_ctor_get(v_lvl_4694_, 0);
        v___x_4697_ = lean_ptr_addr(v_a_4696_);
        v___x_4698_ = lean_ptr_addr(v_newLvl_4695_);
        v___x_4699_ = lean_usize_dec_eq(v___x_4697_, v___x_4698_);
        if v___x_4699_ == 0 {
            let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4700_ = l_Lean_Level_succ___override(v_newLvl_4695_);
            return v___x_4700_;
        } else {
            leanh::lean_dec(v_newLvl_4695_);
            leanh::lean_inc_ref(v_lvl_4694_);
            return v_lvl_4694_;
        }
    } else {
        let mut v___x_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_newLvl_4695_);
        v___x_4701_ = leanh::lean_box(0);
        v___x_4702_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once
            ),
            _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2,
        );
        v___x_4703_ = l_panic___redArg(v___x_4701_, v___x_4702_);
        return v___x_4703_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___boxed(
    mut v_lvl_4704_: *mut leanh::LeanObject,
    mut v_newLvl_4705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4706_ =
        l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_4704_, v_newLvl_4705_);
    leanh::lean_dec(v_lvl_4704_);
    return v_res_4706_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
    v___x_4710_ = leanh::lean_unsigned_to_nat(19);
    v___x_4711_ = leanh::lean_unsigned_to_nat(575);
    v___x_4712_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0;
    v___x_4713_ = l_Lean_Level_mvarId_x21___closed__0;
    v___x_4714_ = l_mkPanicMessageWithDecl(
        v___x_4713_,
        v___x_4712_,
        v___x_4711_,
        v___x_4710_,
        v___x_4709_,
    );
    return v___x_4714_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(
    mut v_lvl_4715_: *mut leanh::LeanObject,
    mut v_newLhs_4716_: *mut leanh::LeanObject,
    mut v_newRhs_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4719_: u8 = 0;
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: usize = 0;
    let mut v___x_4725_: usize = 0;
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4727_: usize = 0;
    let mut v___x_4728_: usize = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_lvl_4715_) == 2 {
                    v_a_4722_ = leanh::lean_ctor_get(v_lvl_4715_, 0);
                    v_a_4723_ = leanh::lean_ctor_get(v_lvl_4715_, 1);
                    v___x_4724_ = lean_ptr_addr(v_a_4722_);
                    v___x_4725_ = lean_ptr_addr(v_newLhs_4716_);
                    v___x_4726_ = lean_usize_dec_eq(v___x_4724_, v___x_4725_);
                    if v___x_4726_ == 0 {
                        v___y_4719_ = v___x_4726_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4727_ = lean_ptr_addr(v_a_4723_);
                        v___x_4728_ = lean_ptr_addr(v_newRhs_4717_);
                        v___x_4729_ = lean_usize_dec_eq(v___x_4727_, v___x_4728_);
                        v___y_4719_ = v___x_4729_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_newRhs_4717_);
                    leanh::lean_dec(v_newLhs_4716_);
                    v___x_4730_ = leanh::lean_box(0);
                    v___x_4731_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once
                        ),
                        _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2,
                    );
                    v___x_4732_ = l_panic___redArg(v___x_4730_, v___x_4731_);
                    return v___x_4732_;
                }
            }
            1 => {
                if v___y_4719_ == 0 {
                    v___x_4720_ = l_Lean_mkLevelMax_x27(v_newLhs_4716_, v_newRhs_4717_);
                    return v___x_4720_;
                } else {
                    v___x_4721_ =
                        l_Lean_simpLevelMax_x27(v_newLhs_4716_, v_newRhs_4717_, v_lvl_4715_);
                    leanh::lean_dec(v_newRhs_4717_);
                    leanh::lean_dec(v_newLhs_4716_);
                    return v___x_4721_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(
    mut v_lvl_4733_: *mut leanh::LeanObject,
    mut v_newLhs_4734_: *mut leanh::LeanObject,
    mut v_newRhs_4735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4736_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(
        v_lvl_4733_,
        v_newLhs_4734_,
        v_newRhs_4735_,
    );
    leanh::lean_dec(v_lvl_4733_);
    return v_res_4736_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
    v___x_4740_ = leanh::lean_unsigned_to_nat(20);
    v___x_4741_ = leanh::lean_unsigned_to_nat(586);
    v___x_4742_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0;
    v___x_4743_ = l_Lean_Level_mvarId_x21___closed__0;
    v___x_4744_ = l_mkPanicMessageWithDecl(
        v___x_4743_,
        v___x_4742_,
        v___x_4741_,
        v___x_4740_,
        v___x_4739_,
    );
    return v___x_4744_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(
    mut v_lvl_4745_: *mut leanh::LeanObject,
    mut v_newLhs_4746_: *mut leanh::LeanObject,
    mut v_newRhs_4747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4749_: u8 = 0;
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: u8 = 0;
    let mut v___x_4757_: usize = 0;
    let mut v___x_4758_: usize = 0;
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_lvl_4745_) == 3 {
                    v_a_4752_ = leanh::lean_ctor_get(v_lvl_4745_, 0);
                    v_a_4753_ = leanh::lean_ctor_get(v_lvl_4745_, 1);
                    v___x_4754_ = lean_ptr_addr(v_a_4752_);
                    v___x_4755_ = lean_ptr_addr(v_newLhs_4746_);
                    v___x_4756_ = lean_usize_dec_eq(v___x_4754_, v___x_4755_);
                    if v___x_4756_ == 0 {
                        v___y_4749_ = v___x_4756_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4757_ = lean_ptr_addr(v_a_4753_);
                        v___x_4758_ = lean_ptr_addr(v_newRhs_4747_);
                        v___x_4759_ = lean_usize_dec_eq(v___x_4757_, v___x_4758_);
                        v___y_4749_ = v___x_4759_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_newRhs_4747_);
                    leanh::lean_dec(v_newLhs_4746_);
                    v___x_4760_ = leanh::lean_box(0);
                    v___x_4761_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once), _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
                    v___x_4762_ = l_panic___redArg(v___x_4760_, v___x_4761_);
                    return v___x_4762_;
                }
            }
            1 => {
                if v___y_4749_ == 0 {
                    v___x_4750_ = l_Lean_mkLevelIMax_x27(v_newLhs_4746_, v_newRhs_4747_);
                    return v___x_4750_;
                } else {
                    v___x_4751_ =
                        l_Lean_simpLevelIMax_x27(v_newLhs_4746_, v_newRhs_4747_, v_lvl_4745_);
                    return v___x_4751_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___boxed(
    mut v_lvl_4763_: *mut leanh::LeanObject,
    mut v_newLhs_4764_: *mut leanh::LeanObject,
    mut v_newRhs_4765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(
        v_lvl_4763_,
        v_newLhs_4764_,
        v_newRhs_4765_,
    );
    leanh::lean_dec(v_lvl_4763_);
    return v_res_4766_;
}
pub unsafe fn l_Lean_Level_mkNaryMax(
    mut v_x_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4767_) == 0 {
        let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4768_ = leanh::lean_box(0);
        return v___x_4768_;
    } else {
        let mut v_tail_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_4769_ = leanh::lean_ctor_get(v_x_4767_, 1);
        if leanh::lean_obj_tag(v_tail_4769_) == 0 {
            let mut v_head_4770_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_4770_ = leanh::lean_ctor_get(v_x_4767_, 0);
            leanh::lean_inc(v_head_4770_);
            leanh::lean_dec_ref_known(v_x_4767_, 2);
            return v_head_4770_;
        } else {
            let mut v_head_4771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4773_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_4769_);
            v_head_4771_ = leanh::lean_ctor_get(v_x_4767_, 0);
            leanh::lean_inc(v_head_4771_);
            leanh::lean_dec_ref_known(v_x_4767_, 2);
            v___x_4772_ = l_Lean_Level_mkNaryMax(v_tail_4769_);
            v___x_4773_ = l_Lean_mkLevelMax_x27(v_head_4771_, v___x_4772_);
            return v___x_4773_;
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_substParams_go(
    mut v_s_4774_: *mut leanh::LeanObject,
    mut v_u_4775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: u8 = 0;
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: u8 = 0;
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: u8 = 0;
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: usize = 0;
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: u8 = 0;
    let mut v_a_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: u8 = 0;
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4804_: u8 = 0;
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: usize = 0;
    let mut v___x_4808_: usize = 0;
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v_a_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_u_4775_) {
                0 => {
                    leanh::lean_dec_ref(v_s_4774_);
                    return v_u_4775_;
                }
                1 => {
                    v_a_4776_ = leanh::lean_ctor_get(v_u_4775_, 0);
                    v___x_4777_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4777_ == 0 {
                        leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        leanh::lean_inc(v_a_4776_);
                        v___x_4778_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4776_,
                        );
                        v___x_4779_ = lean_ptr_addr(v_a_4776_);
                        v___x_4780_ = lean_ptr_addr(v___x_4778_);
                        v___x_4781_ = lean_usize_dec_eq(v___x_4779_, v___x_4780_);
                        if v___x_4781_ == 0 {
                            leanh::lean_dec_ref_known(v_u_4775_, 1);
                            v___x_4782_ = l_Lean_Level_succ___override(v___x_4778_);
                            return v___x_4782_;
                        } else {
                            leanh::lean_dec(v___x_4778_);
                            return v_u_4775_;
                        }
                    }
                }
                2 => {
                    v_a_4783_ = leanh::lean_ctor_get(v_u_4775_, 0);
                    v_a_4784_ = leanh::lean_ctor_get(v_u_4775_, 1);
                    v___x_4785_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4785_ == 0 {
                        leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        leanh::lean_inc(v_a_4783_);
                        leanh::lean_inc_ref(v_s_4774_);
                        v___x_4786_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4783_,
                        );
                        leanh::lean_inc(v_a_4784_);
                        v___x_4787_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4784_,
                        );
                        v___x_4792_ = lean_ptr_addr(v_a_4783_);
                        v___x_4793_ = lean_ptr_addr(v___x_4786_);
                        v___x_4794_ = lean_usize_dec_eq(v___x_4792_, v___x_4793_);
                        if v___x_4794_ == 0 {
                            v___y_4789_ = v___x_4794_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4795_ = lean_ptr_addr(v_a_4784_);
                            v___x_4796_ = lean_ptr_addr(v___x_4787_);
                            v___x_4797_ = lean_usize_dec_eq(v___x_4795_, v___x_4796_);
                            v___y_4789_ = v___x_4797_;
                            state = 1;
                            continue;
                        }
                    }
                }
                3 => {
                    v_a_4798_ = leanh::lean_ctor_get(v_u_4775_, 0);
                    v_a_4799_ = leanh::lean_ctor_get(v_u_4775_, 1);
                    v___x_4800_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4800_ == 0 {
                        leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        leanh::lean_inc(v_a_4798_);
                        leanh::lean_inc_ref(v_s_4774_);
                        v___x_4801_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4798_,
                        );
                        leanh::lean_inc(v_a_4799_);
                        v___x_4802_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4799_,
                        );
                        v___x_4807_ = lean_ptr_addr(v_a_4798_);
                        v___x_4808_ = lean_ptr_addr(v___x_4801_);
                        v___x_4809_ = lean_usize_dec_eq(v___x_4807_, v___x_4808_);
                        if v___x_4809_ == 0 {
                            v___y_4804_ = v___x_4809_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4810_ = lean_ptr_addr(v_a_4799_);
                            v___x_4811_ = lean_ptr_addr(v___x_4802_);
                            v___x_4812_ = lean_usize_dec_eq(v___x_4810_, v___x_4811_);
                            v___y_4804_ = v___x_4812_;
                            state = 2;
                            continue;
                        }
                    }
                }
                4 => {
                    v_a_4813_ = leanh::lean_ctor_get(v_u_4775_, 0);
                    leanh::lean_inc(v_a_4813_);
                    v___x_4814_ = leanh::lean_apply_1(v_s_4774_, v_a_4813_);
                    if leanh::lean_obj_tag(v___x_4814_) == 0 {
                        return v_u_4775_;
                    } else {
                        leanh::lean_dec_ref_known(v_u_4775_, 1);
                        v_val_4815_ = leanh::lean_ctor_get(v___x_4814_, 0);
                        leanh::lean_inc(v_val_4815_);
                        leanh::lean_dec_ref_known(v___x_4814_, 1);
                        return v_val_4815_;
                    }
                }
                _ => {
                    leanh::lean_dec_ref(v_s_4774_);
                    return v_u_4775_;
                }
            },
            1 => {
                if v___y_4789_ == 0 {
                    leanh::lean_dec_ref_known(v_u_4775_, 2);
                    v___x_4790_ = l_Lean_mkLevelMax_x27(v___x_4786_, v___x_4787_);
                    return v___x_4790_;
                } else {
                    v___x_4791_ = l_Lean_simpLevelMax_x27(v___x_4786_, v___x_4787_, v_u_4775_);
                    leanh::lean_dec_ref_known(v_u_4775_, 2);
                    leanh::lean_dec(v___x_4787_);
                    leanh::lean_dec(v___x_4786_);
                    return v___x_4791_;
                }
            }
            2 => {
                if v___y_4804_ == 0 {
                    leanh::lean_dec_ref_known(v_u_4775_, 2);
                    v___x_4805_ = l_Lean_mkLevelIMax_x27(v___x_4801_, v___x_4802_);
                    return v___x_4805_;
                } else {
                    v___x_4806_ = l_Lean_simpLevelIMax_x27(v___x_4801_, v___x_4802_, v_u_4775_);
                    leanh::lean_dec_ref_known(v_u_4775_, 2);
                    return v___x_4806_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_substParams(
    mut v_u_4816_: *mut leanh::LeanObject,
    mut v_s_4817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_4817_, v_u_4816_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_Level_getParamSubst(
    mut v_x_4819_: *mut leanh::LeanObject,
    mut v_x_4820_: *mut leanh::LeanObject,
    mut v_x_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4819_) == 1 {
                    if leanh::lean_obj_tag(v_x_4820_) == 1 {
                        v_head_4822_ = leanh::lean_ctor_get(v_x_4819_, 0);
                        v_tail_4823_ = leanh::lean_ctor_get(v_x_4819_, 1);
                        v_head_4824_ = leanh::lean_ctor_get(v_x_4820_, 0);
                        v_tail_4825_ = leanh::lean_ctor_get(v_x_4820_, 1);
                        v___x_4826_ = lean_name_eq(v_head_4822_, v_x_4821_);
                        if v___x_4826_ == 0 {
                            v_x_4819_ = v_tail_4823_;
                            v_x_4820_ = v_tail_4825_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_inc(v_head_4824_);
                            v___x_4828_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4828_, 0, v_head_4824_);
                            return v___x_4828_;
                        }
                    } else {
                        v___x_4829_ = leanh::lean_box(0);
                        return v___x_4829_;
                    }
                } else {
                    v___x_4830_ = leanh::lean_box(0);
                    return v___x_4830_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_getParamSubst___boxed(
    mut v_x_4831_: *mut leanh::LeanObject,
    mut v_x_4832_: *mut leanh::LeanObject,
    mut v_x_4833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4834_ = l_Lean_Level_getParamSubst(v_x_4831_, v_x_4832_, v_x_4833_);
    leanh::lean_dec(v_x_4833_);
    leanh::lean_dec(v_x_4832_);
    leanh::lean_dec(v_x_4831_);
    return v_res_4834_;
}
pub unsafe fn l_Lean_Level_instantiateParams(
    mut v_u_4835_: *mut leanh::LeanObject,
    mut v_paramNames_4836_: *mut leanh::LeanObject,
    mut v_vs_4837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = leanh::lean_alloc_closure(
        l_Lean_Level_getParamSubst___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_4838_, 0, v_paramNames_4836_);
    leanh::lean_closure_set(v___x_4838_, 1, v_vs_4837_);
    v___x_4839_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_4838_, v_u_4835_);
    return v___x_4839_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go(
    mut v_u_4840_: *mut leanh::LeanObject,
    mut v_v_4841_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_4843_: u8 = 0;
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v_a_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: u8 = 0;
    let mut v_v_x27_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: u8 = 0;
    let mut v___x_4855_: u8 = 0;
    let mut v___y_4857_: u8 = 0;
    let mut v_u_u2081_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_u2082_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: u8 = 0;
    let mut v___x_4865_: u8 = 0;
    let mut v_a_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: u8 = 0;
    let mut v_a_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4864_ = lean_level_eq(v_u_4840_, v_v_4841_);
                if v___x_4864_ == 0 {
                    match leanh::lean_obj_tag(v_v_4841_) {
                        0 => {
                            v___x_4865_ = 1;
                            return v___x_4865_;
                        }
                        2 => {
                            v_a_4866_ = leanh::lean_ctor_get(v_v_4841_, 0);
                            v_a_4867_ = leanh::lean_ctor_get(v_v_4841_, 1);
                            v___x_4868_ =
                                l___private_Lean_Level_0__Lean_Level_geq_go(v_u_4840_, v_a_4866_);
                            if v___x_4868_ == 0 {
                                return v___x_4868_;
                            } else {
                                v_v_4841_ = v_a_4867_;
                                state = 0;
                                continue;
                            }
                        }
                        1 => match leanh::lean_obj_tag(v_u_4840_) {
                            2 => {
                                v_a_4870_ = leanh::lean_ctor_get(v_u_4840_, 0);
                                v_a_4871_ = leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_u2081_4859_ = v_a_4870_;
                                v_u_u2082_4860_ = v_a_4871_;
                                v_v_4861_ = v_v_4841_;
                                state = 4;
                                continue;
                            }
                            3 => {
                                v_a_4872_ = leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_4840_ = v_a_4872_;
                                state = 0;
                                continue;
                            }
                            1 => {
                                v_a_4874_ = leanh::lean_ctor_get(v_v_4841_, 0);
                                v_a_4875_ = leanh::lean_ctor_get(v_u_4840_, 0);
                                v_u_4840_ = v_a_4875_;
                                v_v_4841_ = v_a_4874_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                state = 2;
                                continue;
                            }
                        },
                        _ => match leanh::lean_obj_tag(v_u_4840_) {
                            2 => {
                                v_a_4877_ = leanh::lean_ctor_get(v_u_4840_, 0);
                                v_a_4878_ = leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_u2081_4859_ = v_a_4877_;
                                v_u_u2082_4860_ = v_a_4878_;
                                v_v_4861_ = v_v_4841_;
                                state = 4;
                                continue;
                            }
                            3 => {
                                v_a_4879_ = leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_4840_ = v_a_4879_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                state = 2;
                                continue;
                            }
                        },
                    }
                } else {
                    return v___x_4864_;
                }
            }
            1 => {
                if v___y_4843_ == 0 {
                    return v___y_4843_;
                } else {
                    v___x_4844_ = l_Lean_Level_getOffset(v_v_4841_);
                    v___x_4845_ = l_Lean_Level_getOffset(v_u_4840_);
                    v___x_4846_ = lean_nat_dec_le(v___x_4844_, v___x_4845_);
                    leanh::lean_dec(v___x_4845_);
                    leanh::lean_dec(v___x_4844_);
                    return v___x_4846_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_v_4841_) == 3 {
                    v_a_4848_ = leanh::lean_ctor_get(v_v_4841_, 0);
                    v_a_4849_ = leanh::lean_ctor_get(v_v_4841_, 1);
                    v___x_4850_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_4840_, v_a_4848_);
                    if v___x_4850_ == 0 {
                        return v___x_4850_;
                    } else {
                        v_v_4841_ = v_a_4849_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_v_x27_4852_ = l_Lean_Level_getLevelOffset(v_v_4841_);
                    v___x_4853_ = l_Lean_Level_getLevelOffset(v_u_4840_);
                    v___x_4854_ = lean_level_eq(v___x_4853_, v_v_x27_4852_);
                    leanh::lean_dec(v___x_4853_);
                    if v___x_4854_ == 0 {
                        v___x_4855_ = l_Lean_Level_isZero(v_v_x27_4852_);
                        leanh::lean_dec(v_v_x27_4852_);
                        v___y_4843_ = v___x_4855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_v_x27_4852_);
                        v___y_4843_ = v___x_4854_;
                        state = 1;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_4857_ == 0 {
                    state = 2;
                    continue;
                } else {
                    return v___y_4857_;
                }
            }
            4 => {
                v___x_4862_ =
                    l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2081_4859_, v_v_4861_);
                if v___x_4862_ == 0 {
                    v___x_4863_ =
                        l___private_Lean_Level_0__Lean_Level_geq_go(v_u_u2082_4860_, v_v_4861_);
                    v___y_4857_ = v___x_4863_;
                    state = 3;
                    continue;
                } else {
                    v___y_4857_ = v___x_4862_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go___boxed(
    mut v_u_4881_: *mut leanh::LeanObject,
    mut v_v_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4883_: u8 = 0;
    let mut v_r_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_4881_, v_v_4882_);
    leanh::lean_dec(v_v_4882_);
    leanh::lean_dec(v_u_4881_);
    v_r_4884_ = leanh::lean_box((v_res_4883_) as usize);
    return v_r_4884_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(
    mut v_u_4885_: *mut leanh::LeanObject,
    mut v_v_4886_: *mut leanh::LeanObject,
    mut v_h__1_4887_: *mut leanh::LeanObject,
    mut v_h__2_4888_: *mut leanh::LeanObject,
    mut v_h__3_4889_: *mut leanh::LeanObject,
    mut v_h__4_4890_: *mut leanh::LeanObject,
    mut v_h__5_4891_: *mut leanh::LeanObject,
    mut v_h__6_4892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_v_4886_) {
        0 => {
            let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_4892_);
            leanh::lean_dec(v_h__5_4891_);
            leanh::lean_dec(v_h__4_4890_);
            leanh::lean_dec(v_h__3_4889_);
            leanh::lean_dec(v_h__2_4888_);
            v___x_4893_ = leanh::lean_apply_1(v_h__1_4887_, v_u_4885_);
            return v___x_4893_;
        }
        2 => {
            let mut v_a_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_4895_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_4892_);
            leanh::lean_dec(v_h__5_4891_);
            leanh::lean_dec(v_h__4_4890_);
            leanh::lean_dec(v_h__3_4889_);
            leanh::lean_dec(v_h__1_4887_);
            v_a_4894_ = leanh::lean_ctor_get(v_v_4886_, 0);
            leanh::lean_inc(v_a_4894_);
            v_a_4895_ = leanh::lean_ctor_get(v_v_4886_, 1);
            leanh::lean_inc(v_a_4895_);
            leanh::lean_dec_ref_known(v_v_4886_, 2);
            v___x_4896_ = leanh::lean_apply_3(v_h__2_4888_, v_u_4885_, v_a_4894_, v_a_4895_);
            return v___x_4896_;
        }
        1 => {
            leanh::lean_dec(v_h__2_4888_);
            leanh::lean_dec(v_h__1_4887_);
            match leanh::lean_obj_tag(v_u_4885_) {
                2 => {
                    let mut v_a_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4892_);
                    leanh::lean_dec(v_h__5_4891_);
                    leanh::lean_dec(v_h__4_4890_);
                    v_a_4897_ = leanh::lean_ctor_get(v_u_4885_, 0);
                    leanh::lean_inc(v_a_4897_);
                    v_a_4898_ = leanh::lean_ctor_get(v_u_4885_, 1);
                    leanh::lean_inc(v_a_4898_);
                    leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4899_ = leanh::lean_apply_5(
                        v_h__3_4889_,
                        v_a_4897_,
                        v_a_4898_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4899_;
                }
                3 => {
                    let mut v_a_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4892_);
                    leanh::lean_dec(v_h__5_4891_);
                    leanh::lean_dec(v_h__3_4889_);
                    v_a_4900_ = leanh::lean_ctor_get(v_u_4885_, 0);
                    leanh::lean_inc(v_a_4900_);
                    v_a_4901_ = leanh::lean_ctor_get(v_u_4885_, 1);
                    leanh::lean_inc(v_a_4901_);
                    leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4902_ = leanh::lean_apply_5(
                        v_h__4_4890_,
                        v_a_4900_,
                        v_a_4901_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4902_;
                }
                1 => {
                    let mut v_a_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4892_);
                    leanh::lean_dec(v_h__4_4890_);
                    leanh::lean_dec(v_h__3_4889_);
                    v_a_4903_ = leanh::lean_ctor_get(v_v_4886_, 0);
                    leanh::lean_inc(v_a_4903_);
                    leanh::lean_dec_ref_known(v_v_4886_, 1);
                    v_a_4904_ = leanh::lean_ctor_get(v_u_4885_, 0);
                    leanh::lean_inc(v_a_4904_);
                    leanh::lean_dec_ref_known(v_u_4885_, 1);
                    v___x_4905_ = leanh::lean_apply_2(v_h__5_4891_, v_a_4904_, v_a_4903_);
                    return v___x_4905_;
                }
                _ => {
                    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__5_4891_);
                    leanh::lean_dec(v_h__4_4890_);
                    leanh::lean_dec(v_h__3_4889_);
                    v___x_4906_ = leanh::lean_apply_7(
                        v_h__6_4892_,
                        v_u_4885_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4906_;
                }
            }
        }
        _ => {
            leanh::lean_dec(v_h__5_4891_);
            leanh::lean_dec(v_h__2_4888_);
            leanh::lean_dec(v_h__1_4887_);
            match leanh::lean_obj_tag(v_u_4885_) {
                2 => {
                    let mut v_a_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4892_);
                    leanh::lean_dec(v_h__4_4890_);
                    v_a_4907_ = leanh::lean_ctor_get(v_u_4885_, 0);
                    leanh::lean_inc(v_a_4907_);
                    v_a_4908_ = leanh::lean_ctor_get(v_u_4885_, 1);
                    leanh::lean_inc(v_a_4908_);
                    leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4909_ = leanh::lean_apply_5(
                        v_h__3_4889_,
                        v_a_4907_,
                        v_a_4908_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4909_;
                }
                3 => {
                    let mut v_a_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4892_);
                    leanh::lean_dec(v_h__3_4889_);
                    v_a_4910_ = leanh::lean_ctor_get(v_u_4885_, 0);
                    leanh::lean_inc(v_a_4910_);
                    v_a_4911_ = leanh::lean_ctor_get(v_u_4885_, 1);
                    leanh::lean_inc(v_a_4911_);
                    leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4912_ = leanh::lean_apply_5(
                        v_h__4_4890_,
                        v_a_4910_,
                        v_a_4911_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4912_;
                }
                _ => {
                    let mut v___x_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__4_4890_);
                    leanh::lean_dec(v_h__3_4889_);
                    v___x_4913_ = leanh::lean_apply_7(
                        v_h__6_4892_,
                        v_u_4885_,
                        v_v_4886_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4913_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(
    mut v_motive_4914_: *mut leanh::LeanObject,
    mut v_u_4915_: *mut leanh::LeanObject,
    mut v_v_4916_: *mut leanh::LeanObject,
    mut v_h__1_4917_: *mut leanh::LeanObject,
    mut v_h__2_4918_: *mut leanh::LeanObject,
    mut v_h__3_4919_: *mut leanh::LeanObject,
    mut v_h__4_4920_: *mut leanh::LeanObject,
    mut v_h__5_4921_: *mut leanh::LeanObject,
    mut v_h__6_4922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_v_4916_) {
        0 => {
            let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_4922_);
            leanh::lean_dec(v_h__5_4921_);
            leanh::lean_dec(v_h__4_4920_);
            leanh::lean_dec(v_h__3_4919_);
            leanh::lean_dec(v_h__2_4918_);
            v___x_4923_ = leanh::lean_apply_1(v_h__1_4917_, v_u_4915_);
            return v___x_4923_;
        }
        2 => {
            let mut v_a_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__6_4922_);
            leanh::lean_dec(v_h__5_4921_);
            leanh::lean_dec(v_h__4_4920_);
            leanh::lean_dec(v_h__3_4919_);
            leanh::lean_dec(v_h__1_4917_);
            v_a_4924_ = leanh::lean_ctor_get(v_v_4916_, 0);
            leanh::lean_inc(v_a_4924_);
            v_a_4925_ = leanh::lean_ctor_get(v_v_4916_, 1);
            leanh::lean_inc(v_a_4925_);
            leanh::lean_dec_ref_known(v_v_4916_, 2);
            v___x_4926_ = leanh::lean_apply_3(v_h__2_4918_, v_u_4915_, v_a_4924_, v_a_4925_);
            return v___x_4926_;
        }
        1 => {
            leanh::lean_dec(v_h__2_4918_);
            leanh::lean_dec(v_h__1_4917_);
            match leanh::lean_obj_tag(v_u_4915_) {
                2 => {
                    let mut v_a_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4922_);
                    leanh::lean_dec(v_h__5_4921_);
                    leanh::lean_dec(v_h__4_4920_);
                    v_a_4927_ = leanh::lean_ctor_get(v_u_4915_, 0);
                    leanh::lean_inc(v_a_4927_);
                    v_a_4928_ = leanh::lean_ctor_get(v_u_4915_, 1);
                    leanh::lean_inc(v_a_4928_);
                    leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4929_ = leanh::lean_apply_5(
                        v_h__3_4919_,
                        v_a_4927_,
                        v_a_4928_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4929_;
                }
                3 => {
                    let mut v_a_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4922_);
                    leanh::lean_dec(v_h__5_4921_);
                    leanh::lean_dec(v_h__3_4919_);
                    v_a_4930_ = leanh::lean_ctor_get(v_u_4915_, 0);
                    leanh::lean_inc(v_a_4930_);
                    v_a_4931_ = leanh::lean_ctor_get(v_u_4915_, 1);
                    leanh::lean_inc(v_a_4931_);
                    leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4932_ = leanh::lean_apply_5(
                        v_h__4_4920_,
                        v_a_4930_,
                        v_a_4931_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4932_;
                }
                1 => {
                    let mut v_a_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4922_);
                    leanh::lean_dec(v_h__4_4920_);
                    leanh::lean_dec(v_h__3_4919_);
                    v_a_4933_ = leanh::lean_ctor_get(v_v_4916_, 0);
                    leanh::lean_inc(v_a_4933_);
                    leanh::lean_dec_ref_known(v_v_4916_, 1);
                    v_a_4934_ = leanh::lean_ctor_get(v_u_4915_, 0);
                    leanh::lean_inc(v_a_4934_);
                    leanh::lean_dec_ref_known(v_u_4915_, 1);
                    v___x_4935_ = leanh::lean_apply_2(v_h__5_4921_, v_a_4934_, v_a_4933_);
                    return v___x_4935_;
                }
                _ => {
                    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__5_4921_);
                    leanh::lean_dec(v_h__4_4920_);
                    leanh::lean_dec(v_h__3_4919_);
                    v___x_4936_ = leanh::lean_apply_7(
                        v_h__6_4922_,
                        v_u_4915_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4936_;
                }
            }
        }
        _ => {
            leanh::lean_dec(v_h__5_4921_);
            leanh::lean_dec(v_h__2_4918_);
            leanh::lean_dec(v_h__1_4917_);
            match leanh::lean_obj_tag(v_u_4915_) {
                2 => {
                    let mut v_a_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4922_);
                    leanh::lean_dec(v_h__4_4920_);
                    v_a_4937_ = leanh::lean_ctor_get(v_u_4915_, 0);
                    leanh::lean_inc(v_a_4937_);
                    v_a_4938_ = leanh::lean_ctor_get(v_u_4915_, 1);
                    leanh::lean_inc(v_a_4938_);
                    leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4939_ = leanh::lean_apply_5(
                        v_h__3_4919_,
                        v_a_4937_,
                        v_a_4938_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4939_;
                }
                3 => {
                    let mut v_a_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__6_4922_);
                    leanh::lean_dec(v_h__3_4919_);
                    v_a_4940_ = leanh::lean_ctor_get(v_u_4915_, 0);
                    leanh::lean_inc(v_a_4940_);
                    v_a_4941_ = leanh::lean_ctor_get(v_u_4915_, 1);
                    leanh::lean_inc(v_a_4941_);
                    leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4942_ = leanh::lean_apply_5(
                        v_h__4_4920_,
                        v_a_4940_,
                        v_a_4941_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4942_;
                }
                _ => {
                    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v_h__4_4920_);
                    leanh::lean_dec(v_h__3_4919_);
                    v___x_4943_ = leanh::lean_apply_7(
                        v_h__6_4922_,
                        v_u_4915_,
                        v_v_4916_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                    );
                    return v___x_4943_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(
    mut v_x_4944_: *mut leanh::LeanObject,
    mut v_h__1_4945_: *mut leanh::LeanObject,
    mut v_h__2_4946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4944_) == 3 {
        let mut v_a_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4946_);
        v_a_4947_ = leanh::lean_ctor_get(v_x_4944_, 0);
        leanh::lean_inc(v_a_4947_);
        v_a_4948_ = leanh::lean_ctor_get(v_x_4944_, 1);
        leanh::lean_inc(v_a_4948_);
        leanh::lean_dec_ref_known(v_x_4944_, 2);
        v___x_4949_ = leanh::lean_apply_2(v_h__1_4945_, v_a_4947_, v_a_4948_);
        return v___x_4949_;
    } else {
        let mut v___x_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4945_);
        v___x_4950_ =
            leanh::lean_apply_2(v_h__2_4946_, v_x_4944_, leanh::lean_box(0));
        return v___x_4950_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(
    mut v_motive_4951_: *mut leanh::LeanObject,
    mut v_x_4952_: *mut leanh::LeanObject,
    mut v_h__1_4953_: *mut leanh::LeanObject,
    mut v_h__2_4954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4952_) == 3 {
        let mut v_a_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_4954_);
        v_a_4955_ = leanh::lean_ctor_get(v_x_4952_, 0);
        leanh::lean_inc(v_a_4955_);
        v_a_4956_ = leanh::lean_ctor_get(v_x_4952_, 1);
        leanh::lean_inc(v_a_4956_);
        leanh::lean_dec_ref_known(v_x_4952_, 2);
        v___x_4957_ = leanh::lean_apply_2(v_h__1_4953_, v_a_4955_, v_a_4956_);
        return v___x_4957_;
    } else {
        let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_4953_);
        v___x_4958_ =
            leanh::lean_apply_2(v_h__2_4954_, v_x_4952_, leanh::lean_box(0));
        return v___x_4958_;
    }
}
pub unsafe fn l_Lean_Level_geq(
    mut v_u_4959_: *mut leanh::LeanObject,
    mut v_v_4960_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: u8 = 0;
    v___x_4961_ = l_Lean_Level_normalize(v_u_4959_);
    v___x_4962_ = l_Lean_Level_normalize(v_v_4960_);
    v___x_4963_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_4961_, v___x_4962_);
    leanh::lean_dec(v___x_4962_);
    leanh::lean_dec(v___x_4961_);
    return v___x_4963_;
}
pub unsafe fn l_Lean_Level_geq___boxed(
    mut v_u_4964_: *mut leanh::LeanObject,
    mut v_v_4965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4966_: u8 = 0;
    let mut v_r_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4966_ = l_Lean_Level_geq(v_u_4964_, v_v_4965_);
    leanh::lean_dec(v_v_4965_);
    leanh::lean_dec(v_u_4964_);
    v_r_4967_ = leanh::lean_box((v_res_4966_) as usize);
    return v_r_4967_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(
    mut v_k_4968_: *mut leanh::LeanObject,
    mut v_v_4969_: *mut leanh::LeanObject,
    mut v_t_4970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4979_: u8 = 0;
    let mut v_impl_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v_size_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5010_: u8 = 0;
    let mut v___x_5011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_unused_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut v_unused_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5061_: u8 = 0;
    let mut v_unused_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5073_: u8 = 0;
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5081_: u8 = 0;
    let mut v_unused_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5089_: u8 = 0;
    let mut v_k_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v_unused_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_5120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v___x_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v_size_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut v_unused_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5188_: u8 = 0;
    let mut v___x_5190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5199_: u8 = 0;
    let mut v_unused_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v_k_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5227_: u8 = 0;
    let mut v_unused_5228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut v_unused_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5239_: u8 = 0;
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_unused_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v___x_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_4970_) == 0 {
                    v_size_4971_ = leanh::lean_ctor_get(v_t_4970_, 0);
                    v_k_4972_ = leanh::lean_ctor_get(v_t_4970_, 1);
                    v_v_4973_ = leanh::lean_ctor_get(v_t_4970_, 2);
                    v_l_4974_ = leanh::lean_ctor_get(v_t_4970_, 3);
                    v_r_4975_ = leanh::lean_ctor_get(v_t_4970_, 4);
                    v_isSharedCheck_5255_ = (!leanh::lean_is_exclusive(v_t_4970_)) as u8;
                    if v_isSharedCheck_5255_ == 0 {
                        v___x_4977_ = v_t_4970_;
                        v_isShared_4978_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_4975_);
                        leanh::lean_inc(v_l_4974_);
                        leanh::lean_inc(v_v_4973_);
                        leanh::lean_inc(v_k_4972_);
                        leanh::lean_inc(v_size_4971_);
                        leanh::lean_dec(v_t_4970_);
                        v___x_4977_ = leanh::lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5256_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5257_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_5257_, 0, v___x_5256_);
                    leanh::lean_ctor_set(v___x_5257_, 1, v_k_4968_);
                    leanh::lean_ctor_set(v___x_5257_, 2, v_v_4969_);
                    leanh::lean_ctor_set(v___x_5257_, 3, v_t_4970_);
                    leanh::lean_ctor_set(v___x_5257_, 4, v_t_4970_);
                    return v___x_5257_;
                }
            }
            1 => {
                v___x_4979_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4968_, v_k_4972_);
                match v___x_4979_ {
                    0 => {
                        leanh::lean_dec(v_size_4971_);
                        v_impl_4980_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_4968_, v_v_4969_, v_l_4974_);
                        v___x_4981_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_r_4975_) == 0 {
                            v_size_4982_ = leanh::lean_ctor_get(v_r_4975_, 0);
                            v_size_4983_ = leanh::lean_ctor_get(v_impl_4980_, 0);
                            leanh::lean_inc(v_size_4983_);
                            v_k_4984_ = leanh::lean_ctor_get(v_impl_4980_, 1);
                            leanh::lean_inc(v_k_4984_);
                            v_v_4985_ = leanh::lean_ctor_get(v_impl_4980_, 2);
                            leanh::lean_inc(v_v_4985_);
                            v_l_4986_ = leanh::lean_ctor_get(v_impl_4980_, 3);
                            leanh::lean_inc(v_l_4986_);
                            v_r_4987_ = leanh::lean_ctor_get(v_impl_4980_, 4);
                            leanh::lean_inc(v_r_4987_);
                            v___x_4988_ = leanh::lean_unsigned_to_nat(3);
                            v___x_4989_ = lean_nat_mul(v___x_4988_, v_size_4982_);
                            v___x_4990_ = lean_nat_dec_lt(v___x_4989_, v_size_4983_);
                            leanh::lean_dec(v___x_4989_);
                            if v___x_4990_ == 0 {
                                leanh::lean_dec(v_r_4987_);
                                leanh::lean_dec(v_l_4986_);
                                leanh::lean_dec(v_v_4985_);
                                leanh::lean_dec(v_k_4984_);
                                v___x_4991_ = lean_nat_add(v___x_4981_, v_size_4983_);
                                leanh::lean_dec(v_size_4983_);
                                v___x_4992_ = lean_nat_add(v___x_4991_, v_size_4982_);
                                leanh::lean_dec(v___x_4991_);
                                if v_isShared_4978_ == 0 {
                                    leanh::lean_ctor_set(v___x_4977_, 3, v_impl_4980_);
                                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_4992_);
                                    v___x_4994_ = v___x_4977_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4995_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        0,
                                        v___x_4992_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        1,
                                        v_k_4972_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        2,
                                        v_v_4973_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        3,
                                        v_impl_4980_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        4,
                                        v_r_4975_,
                                    );
                                    v___x_4994_ = v_reuseFailAlloc_4995_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_5061_ =
                                    (!leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                if v_isSharedCheck_5061_ == 0 {
                                    v_unused_5062_ = leanh::lean_ctor_get(v_impl_4980_, 4);
                                    leanh::lean_dec(v_unused_5062_);
                                    v_unused_5063_ = leanh::lean_ctor_get(v_impl_4980_, 3);
                                    leanh::lean_dec(v_unused_5063_);
                                    v_unused_5064_ = leanh::lean_ctor_get(v_impl_4980_, 2);
                                    leanh::lean_dec(v_unused_5064_);
                                    v_unused_5065_ = leanh::lean_ctor_get(v_impl_4980_, 1);
                                    leanh::lean_dec(v_unused_5065_);
                                    v_unused_5066_ = leanh::lean_ctor_get(v_impl_4980_, 0);
                                    leanh::lean_dec(v_unused_5066_);
                                    v___x_4997_ = v_impl_4980_;
                                    v_isShared_4998_ = v_isSharedCheck_5061_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_4980_);
                                    v___x_4997_ = leanh::lean_box(0);
                                    v_isShared_4998_ = v_isSharedCheck_5061_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_5067_ = leanh::lean_ctor_get(v_impl_4980_, 3);
                            leanh::lean_inc(v_l_5067_);
                            if leanh::lean_obj_tag(v_l_5067_) == 0 {
                                v_r_5068_ = leanh::lean_ctor_get(v_impl_4980_, 4);
                                v_k_5069_ = leanh::lean_ctor_get(v_impl_4980_, 1);
                                v_v_5070_ = leanh::lean_ctor_get(v_impl_4980_, 2);
                                v_isSharedCheck_5081_ =
                                    (!leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                if v_isSharedCheck_5081_ == 0 {
                                    v_unused_5082_ = leanh::lean_ctor_get(v_impl_4980_, 3);
                                    leanh::lean_dec(v_unused_5082_);
                                    v_unused_5083_ = leanh::lean_ctor_get(v_impl_4980_, 0);
                                    leanh::lean_dec(v_unused_5083_);
                                    v___x_5072_ = v_impl_4980_;
                                    v_isShared_5073_ = v_isSharedCheck_5081_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_5068_);
                                    leanh::lean_inc(v_v_5070_);
                                    leanh::lean_inc(v_k_5069_);
                                    leanh::lean_dec(v_impl_4980_);
                                    v___x_5072_ = leanh::lean_box(0);
                                    v_isShared_5073_ = v_isSharedCheck_5081_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_5084_ = leanh::lean_ctor_get(v_impl_4980_, 4);
                                leanh::lean_inc(v_r_5084_);
                                if leanh::lean_obj_tag(v_r_5084_) == 0 {
                                    v_k_5085_ = leanh::lean_ctor_get(v_impl_4980_, 1);
                                    v_v_5086_ = leanh::lean_ctor_get(v_impl_4980_, 2);
                                    v_isSharedCheck_5109_ =
                                        (!leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                    if v_isSharedCheck_5109_ == 0 {
                                        v_unused_5110_ =
                                            leanh::lean_ctor_get(v_impl_4980_, 4);
                                        leanh::lean_dec(v_unused_5110_);
                                        v_unused_5111_ =
                                            leanh::lean_ctor_get(v_impl_4980_, 3);
                                        leanh::lean_dec(v_unused_5111_);
                                        v_unused_5112_ =
                                            leanh::lean_ctor_get(v_impl_4980_, 0);
                                        leanh::lean_dec(v_unused_5112_);
                                        v___x_5088_ = v_impl_4980_;
                                        v_isShared_5089_ = v_isSharedCheck_5109_;
                                        state = 16;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_5086_);
                                        leanh::lean_inc(v_k_5085_);
                                        leanh::lean_dec(v_impl_4980_);
                                        v___x_5088_ = leanh::lean_box(0);
                                        v_isShared_5089_ = v_isSharedCheck_5109_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_5113_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4978_ == 0 {
                                        leanh::lean_ctor_set(v___x_4977_, 4, v_r_5084_);
                                        leanh::lean_ctor_set(v___x_4977_, 3, v_impl_4980_);
                                        leanh::lean_ctor_set(v___x_4977_, 0, v___x_5113_);
                                        v___x_5115_ = v___x_4977_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5116_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            0,
                                            v___x_5113_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            1,
                                            v_k_4972_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            2,
                                            v_v_4973_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            3,
                                            v_impl_4980_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            4,
                                            v_r_5084_,
                                        );
                                        v___x_5115_ = v_reuseFailAlloc_5116_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        leanh::lean_dec(v_v_4973_);
                        leanh::lean_dec(v_k_4972_);
                        if v_isShared_4978_ == 0 {
                            leanh::lean_ctor_set(v___x_4977_, 2, v_v_4969_);
                            leanh::lean_ctor_set(v___x_4977_, 1, v_k_4968_);
                            v___x_5118_ = v___x_4977_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_5119_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_size_4971_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_k_4968_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 2, v_v_4969_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 3, v_l_4974_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 4, v_r_4975_);
                            v___x_5118_ = v_reuseFailAlloc_5119_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_4971_);
                        v_impl_5120_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_4968_, v_v_4969_, v_r_4975_);
                        v___x_5121_ = leanh::lean_unsigned_to_nat(1);
                        if leanh::lean_obj_tag(v_l_4974_) == 0 {
                            v_size_5122_ = leanh::lean_ctor_get(v_l_4974_, 0);
                            v_size_5123_ = leanh::lean_ctor_get(v_impl_5120_, 0);
                            leanh::lean_inc(v_size_5123_);
                            v_k_5124_ = leanh::lean_ctor_get(v_impl_5120_, 1);
                            leanh::lean_inc(v_k_5124_);
                            v_v_5125_ = leanh::lean_ctor_get(v_impl_5120_, 2);
                            leanh::lean_inc(v_v_5125_);
                            v_l_5126_ = leanh::lean_ctor_get(v_impl_5120_, 3);
                            leanh::lean_inc(v_l_5126_);
                            v_r_5127_ = leanh::lean_ctor_get(v_impl_5120_, 4);
                            leanh::lean_inc(v_r_5127_);
                            v___x_5128_ = leanh::lean_unsigned_to_nat(3);
                            v___x_5129_ = lean_nat_mul(v___x_5128_, v_size_5122_);
                            v___x_5130_ = lean_nat_dec_lt(v___x_5129_, v_size_5123_);
                            leanh::lean_dec(v___x_5129_);
                            if v___x_5130_ == 0 {
                                leanh::lean_dec(v_r_5127_);
                                leanh::lean_dec(v_l_5126_);
                                leanh::lean_dec(v_v_5125_);
                                leanh::lean_dec(v_k_5124_);
                                v___x_5131_ = lean_nat_add(v___x_5121_, v_size_5122_);
                                v___x_5132_ = lean_nat_add(v___x_5131_, v_size_5123_);
                                leanh::lean_dec(v_size_5123_);
                                leanh::lean_dec(v___x_5131_);
                                if v_isShared_4978_ == 0 {
                                    leanh::lean_ctor_set(v___x_4977_, 4, v_impl_5120_);
                                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5132_);
                                    v___x_5134_ = v___x_4977_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5135_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        0,
                                        v___x_5132_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        1,
                                        v_k_4972_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        2,
                                        v_v_4973_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        3,
                                        v_l_4974_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        4,
                                        v_impl_5120_,
                                    );
                                    v___x_5134_ = v_reuseFailAlloc_5135_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_5199_ =
                                    (!leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                if v_isSharedCheck_5199_ == 0 {
                                    v_unused_5200_ = leanh::lean_ctor_get(v_impl_5120_, 4);
                                    leanh::lean_dec(v_unused_5200_);
                                    v_unused_5201_ = leanh::lean_ctor_get(v_impl_5120_, 3);
                                    leanh::lean_dec(v_unused_5201_);
                                    v_unused_5202_ = leanh::lean_ctor_get(v_impl_5120_, 2);
                                    leanh::lean_dec(v_unused_5202_);
                                    v_unused_5203_ = leanh::lean_ctor_get(v_impl_5120_, 1);
                                    leanh::lean_dec(v_unused_5203_);
                                    v_unused_5204_ = leanh::lean_ctor_get(v_impl_5120_, 0);
                                    leanh::lean_dec(v_unused_5204_);
                                    v___x_5137_ = v_impl_5120_;
                                    v_isShared_5138_ = v_isSharedCheck_5199_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_impl_5120_);
                                    v___x_5137_ = leanh::lean_box(0);
                                    v_isShared_5138_ = v_isSharedCheck_5199_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_5205_ = leanh::lean_ctor_get(v_impl_5120_, 3);
                            leanh::lean_inc(v_l_5205_);
                            if leanh::lean_obj_tag(v_l_5205_) == 0 {
                                v_r_5206_ = leanh::lean_ctor_get(v_impl_5120_, 4);
                                v_k_5207_ = leanh::lean_ctor_get(v_impl_5120_, 1);
                                v_v_5208_ = leanh::lean_ctor_get(v_impl_5120_, 2);
                                v_isSharedCheck_5231_ =
                                    (!leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                if v_isSharedCheck_5231_ == 0 {
                                    v_unused_5232_ = leanh::lean_ctor_get(v_impl_5120_, 3);
                                    leanh::lean_dec(v_unused_5232_);
                                    v_unused_5233_ = leanh::lean_ctor_get(v_impl_5120_, 0);
                                    leanh::lean_dec(v_unused_5233_);
                                    v___x_5210_ = v_impl_5120_;
                                    v_isShared_5211_ = v_isSharedCheck_5231_;
                                    state = 34;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_r_5206_);
                                    leanh::lean_inc(v_v_5208_);
                                    leanh::lean_inc(v_k_5207_);
                                    leanh::lean_dec(v_impl_5120_);
                                    v___x_5210_ = leanh::lean_box(0);
                                    v_isShared_5211_ = v_isSharedCheck_5231_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_5234_ = leanh::lean_ctor_get(v_impl_5120_, 4);
                                leanh::lean_inc(v_r_5234_);
                                if leanh::lean_obj_tag(v_r_5234_) == 0 {
                                    v_k_5235_ = leanh::lean_ctor_get(v_impl_5120_, 1);
                                    v_v_5236_ = leanh::lean_ctor_get(v_impl_5120_, 2);
                                    v_isSharedCheck_5247_ =
                                        (!leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                    if v_isSharedCheck_5247_ == 0 {
                                        v_unused_5248_ =
                                            leanh::lean_ctor_get(v_impl_5120_, 4);
                                        leanh::lean_dec(v_unused_5248_);
                                        v_unused_5249_ =
                                            leanh::lean_ctor_get(v_impl_5120_, 3);
                                        leanh::lean_dec(v_unused_5249_);
                                        v_unused_5250_ =
                                            leanh::lean_ctor_get(v_impl_5120_, 0);
                                        leanh::lean_dec(v_unused_5250_);
                                        v___x_5238_ = v_impl_5120_;
                                        v_isShared_5239_ = v_isSharedCheck_5247_;
                                        state = 39;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_v_5236_);
                                        leanh::lean_inc(v_k_5235_);
                                        leanh::lean_dec(v_impl_5120_);
                                        v___x_5238_ = leanh::lean_box(0);
                                        v_isShared_5239_ = v_isSharedCheck_5247_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_5251_ = leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4978_ == 0 {
                                        leanh::lean_ctor_set(v___x_4977_, 4, v_impl_5120_);
                                        leanh::lean_ctor_set(v___x_4977_, 3, v_r_5234_);
                                        leanh::lean_ctor_set(v___x_4977_, 0, v___x_5251_);
                                        v___x_5253_ = v___x_4977_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5254_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            0,
                                            v___x_5251_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            1,
                                            v_k_4972_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            2,
                                            v_v_4973_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            3,
                                            v_r_5234_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            4,
                                            v_impl_5120_,
                                        );
                                        v___x_5253_ = v_reuseFailAlloc_5254_;
                                        state = 42;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_4994_;
            }
            3 => {
                v_size_4999_ = leanh::lean_ctor_get(v_l_4986_, 0);
                v_size_5000_ = leanh::lean_ctor_get(v_r_4987_, 0);
                v_k_5001_ = leanh::lean_ctor_get(v_r_4987_, 1);
                v_v_5002_ = leanh::lean_ctor_get(v_r_4987_, 2);
                v_l_5003_ = leanh::lean_ctor_get(v_r_4987_, 3);
                v_r_5004_ = leanh::lean_ctor_get(v_r_4987_, 4);
                v___x_5005_ = leanh::lean_unsigned_to_nat(2);
                v___x_5006_ = lean_nat_mul(v___x_5005_, v_size_4999_);
                v___x_5007_ = lean_nat_dec_lt(v_size_5000_, v___x_5006_);
                leanh::lean_dec(v___x_5006_);
                if v___x_5007_ == 0 {
                    leanh::lean_inc(v_r_5004_);
                    leanh::lean_inc(v_l_5003_);
                    leanh::lean_inc(v_v_5002_);
                    leanh::lean_inc(v_k_5001_);
                    v_isSharedCheck_5036_ = (!leanh::lean_is_exclusive(v_r_4987_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v_unused_5037_ = leanh::lean_ctor_get(v_r_4987_, 4);
                        leanh::lean_dec(v_unused_5037_);
                        v_unused_5038_ = leanh::lean_ctor_get(v_r_4987_, 3);
                        leanh::lean_dec(v_unused_5038_);
                        v_unused_5039_ = leanh::lean_ctor_get(v_r_4987_, 2);
                        leanh::lean_dec(v_unused_5039_);
                        v_unused_5040_ = leanh::lean_ctor_get(v_r_4987_, 1);
                        leanh::lean_dec(v_unused_5040_);
                        v_unused_5041_ = leanh::lean_ctor_get(v_r_4987_, 0);
                        leanh::lean_dec(v_unused_5041_);
                        v___x_5009_ = v_r_4987_;
                        v_isShared_5010_ = v_isSharedCheck_5036_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v_r_4987_);
                        v___x_5009_ = leanh::lean_box(0);
                        v_isShared_5010_ = v_isSharedCheck_5036_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4977_);
                    v___x_5042_ = lean_nat_add(v___x_4981_, v_size_4983_);
                    leanh::lean_dec(v_size_4983_);
                    v___x_5043_ = lean_nat_add(v___x_5042_, v_size_4982_);
                    leanh::lean_dec(v___x_5042_);
                    v___x_5044_ = lean_nat_add(v___x_4981_, v_size_4982_);
                    v___x_5045_ = lean_nat_add(v___x_5044_, v_size_5000_);
                    leanh::lean_dec(v___x_5044_);
                    leanh::lean_inc_ref(v_r_4975_);
                    if v_isShared_4998_ == 0 {
                        leanh::lean_ctor_set(v___x_4997_, 4, v_r_4975_);
                        leanh::lean_ctor_set(v___x_4997_, 3, v_r_4987_);
                        leanh::lean_ctor_set(v___x_4997_, 2, v_v_4973_);
                        leanh::lean_ctor_set(v___x_4997_, 1, v_k_4972_);
                        leanh::lean_ctor_set(v___x_4997_, 0, v___x_5045_);
                        v___x_5047_ = v___x_4997_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5060_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5045_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_k_4972_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 2, v_v_4973_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 3, v_r_4987_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 4, v_r_4975_);
                        v___x_5047_ = v_reuseFailAlloc_5060_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5011_ = lean_nat_add(v___x_4981_, v_size_4983_);
                leanh::lean_dec(v_size_4983_);
                v___x_5012_ = lean_nat_add(v___x_5011_, v_size_4982_);
                leanh::lean_dec(v___x_5011_);
                v___x_5024_ = lean_nat_add(v___x_4981_, v_size_4999_);
                if leanh::lean_obj_tag(v_l_5003_) == 0 {
                    v_size_5034_ = leanh::lean_ctor_get(v_l_5003_, 0);
                    leanh::lean_inc(v_size_5034_);
                    v___y_5026_ = v_size_5034_;
                    state = 8;
                    continue;
                } else {
                    v___x_5035_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5026_ = v___x_5035_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_5017_ = lean_nat_add(v___y_5015_, v___y_5016_);
                leanh::lean_dec(v___y_5016_);
                leanh::lean_dec(v___y_5015_);
                if v_isShared_5010_ == 0 {
                    leanh::lean_ctor_set(v___x_5009_, 4, v_r_4975_);
                    leanh::lean_ctor_set(v___x_5009_, 3, v_r_5004_);
                    leanh::lean_ctor_set(v___x_5009_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v___x_5009_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v___x_5009_, 0, v___x_5017_);
                    v___x_5019_ = v___x_5009_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 3, v_r_5004_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 4, v_r_4975_);
                    v___x_5019_ = v_reuseFailAlloc_5023_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4998_ == 0 {
                    leanh::lean_ctor_set(v___x_4997_, 4, v___x_5019_);
                    leanh::lean_ctor_set(v___x_4997_, 3, v___y_5014_);
                    leanh::lean_ctor_set(v___x_4997_, 2, v_v_5002_);
                    leanh::lean_ctor_set(v___x_4997_, 1, v_k_5001_);
                    leanh::lean_ctor_set(v___x_4997_, 0, v___x_5012_);
                    v___x_5021_ = v___x_4997_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5012_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_k_5001_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_v_5002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 3, v___y_5014_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 4, v___x_5019_);
                    v___x_5021_ = v_reuseFailAlloc_5022_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5021_;
            }
            8 => {
                v___x_5027_ = lean_nat_add(v___x_5024_, v___y_5026_);
                leanh::lean_dec(v___y_5026_);
                leanh::lean_dec(v___x_5024_);
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v_l_5003_);
                    leanh::lean_ctor_set(v___x_4977_, 3, v_l_4986_);
                    leanh::lean_ctor_set(v___x_4977_, 2, v_v_4985_);
                    leanh::lean_ctor_set(v___x_4977_, 1, v_k_4984_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5027_);
                    v___x_5029_ = v___x_4977_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5033_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 1, v_k_4984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 2, v_v_4985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 3, v_l_4986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 4, v_l_5003_);
                    v___x_5029_ = v_reuseFailAlloc_5033_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5030_ = lean_nat_add(v___x_4981_, v_size_4982_);
                if leanh::lean_obj_tag(v_r_5004_) == 0 {
                    v_size_5031_ = leanh::lean_ctor_get(v_r_5004_, 0);
                    leanh::lean_inc(v_size_5031_);
                    v___y_5014_ = v___x_5029_;
                    v___y_5015_ = v___x_5030_;
                    v___y_5016_ = v_size_5031_;
                    state = 5;
                    continue;
                } else {
                    v___x_5032_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5014_ = v___x_5029_;
                    v___y_5015_ = v___x_5030_;
                    v___y_5016_ = v___x_5032_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_5054_ = (!leanh::lean_is_exclusive(v_r_4975_)) as u8;
                if v_isSharedCheck_5054_ == 0 {
                    v_unused_5055_ = leanh::lean_ctor_get(v_r_4975_, 4);
                    leanh::lean_dec(v_unused_5055_);
                    v_unused_5056_ = leanh::lean_ctor_get(v_r_4975_, 3);
                    leanh::lean_dec(v_unused_5056_);
                    v_unused_5057_ = leanh::lean_ctor_get(v_r_4975_, 2);
                    leanh::lean_dec(v_unused_5057_);
                    v_unused_5058_ = leanh::lean_ctor_get(v_r_4975_, 1);
                    leanh::lean_dec(v_unused_5058_);
                    v_unused_5059_ = leanh::lean_ctor_get(v_r_4975_, 0);
                    leanh::lean_dec(v_unused_5059_);
                    v___x_5049_ = v_r_4975_;
                    v_isShared_5050_ = v_isSharedCheck_5054_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_4975_);
                    v___x_5049_ = leanh::lean_box(0);
                    v_isShared_5050_ = v_isSharedCheck_5054_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5050_ == 0 {
                    leanh::lean_ctor_set(v___x_5049_, 4, v___x_5047_);
                    leanh::lean_ctor_set(v___x_5049_, 3, v_l_4986_);
                    leanh::lean_ctor_set(v___x_5049_, 2, v_v_4985_);
                    leanh::lean_ctor_set(v___x_5049_, 1, v_k_4984_);
                    leanh::lean_ctor_set(v___x_5049_, 0, v___x_5043_);
                    v___x_5052_ = v___x_5049_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5053_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5043_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 1, v_k_4984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 2, v_v_4985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 3, v_l_4986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 4, v___x_5047_);
                    v___x_5052_ = v_reuseFailAlloc_5053_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5052_;
            }
            13 => {
                v___x_5074_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc(v_r_5068_);
                if v_isShared_5073_ == 0 {
                    leanh::lean_ctor_set(v___x_5072_, 3, v_r_5068_);
                    leanh::lean_ctor_set(v___x_5072_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v___x_5072_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v___x_5072_, 0, v___x_4981_);
                    v___x_5076_ = v___x_5072_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_4981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 3, v_r_5068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 4, v_r_5068_);
                    v___x_5076_ = v_reuseFailAlloc_5080_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v___x_5076_);
                    leanh::lean_ctor_set(v___x_4977_, 3, v_l_5067_);
                    leanh::lean_ctor_set(v___x_4977_, 2, v_v_5070_);
                    leanh::lean_ctor_set(v___x_4977_, 1, v_k_5069_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5074_);
                    v___x_5078_ = v___x_4977_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5079_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_k_5069_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_v_5070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_l_5067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 4, v___x_5076_);
                    v___x_5078_ = v_reuseFailAlloc_5079_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5078_;
            }
            16 => {
                v_k_5090_ = leanh::lean_ctor_get(v_r_5084_, 1);
                v_v_5091_ = leanh::lean_ctor_get(v_r_5084_, 2);
                v_isSharedCheck_5105_ = (!leanh::lean_is_exclusive(v_r_5084_)) as u8;
                if v_isSharedCheck_5105_ == 0 {
                    v_unused_5106_ = leanh::lean_ctor_get(v_r_5084_, 4);
                    leanh::lean_dec(v_unused_5106_);
                    v_unused_5107_ = leanh::lean_ctor_get(v_r_5084_, 3);
                    leanh::lean_dec(v_unused_5107_);
                    v_unused_5108_ = leanh::lean_ctor_get(v_r_5084_, 0);
                    leanh::lean_dec(v_unused_5108_);
                    v___x_5093_ = v_r_5084_;
                    v_isShared_5094_ = v_isSharedCheck_5105_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_inc(v_v_5091_);
                    leanh::lean_inc(v_k_5090_);
                    leanh::lean_dec(v_r_5084_);
                    v___x_5093_ = leanh::lean_box(0);
                    v_isShared_5094_ = v_isSharedCheck_5105_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_5095_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_5094_ == 0 {
                    leanh::lean_ctor_set(v___x_5093_, 4, v_l_5067_);
                    leanh::lean_ctor_set(v___x_5093_, 3, v_l_5067_);
                    leanh::lean_ctor_set(v___x_5093_, 2, v_v_5086_);
                    leanh::lean_ctor_set(v___x_5093_, 1, v_k_5085_);
                    leanh::lean_ctor_set(v___x_5093_, 0, v___x_4981_);
                    v___x_5097_ = v___x_5093_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_4981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 1, v_k_5085_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 2, v_v_5086_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 3, v_l_5067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 4, v_l_5067_);
                    v___x_5097_ = v_reuseFailAlloc_5104_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_5089_ == 0 {
                    leanh::lean_ctor_set(v___x_5088_, 4, v_l_5067_);
                    leanh::lean_ctor_set(v___x_5088_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v___x_5088_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v___x_5088_, 0, v___x_4981_);
                    v___x_5099_ = v___x_5088_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_4981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_l_5067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_l_5067_);
                    v___x_5099_ = v_reuseFailAlloc_5103_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v___x_5099_);
                    leanh::lean_ctor_set(v___x_4977_, 3, v___x_5097_);
                    leanh::lean_ctor_set(v___x_4977_, 2, v_v_5091_);
                    leanh::lean_ctor_set(v___x_4977_, 1, v_k_5090_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5095_);
                    v___x_5101_ = v___x_4977_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5102_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5095_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_k_5090_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 2, v_v_5091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 3, v___x_5097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 4, v___x_5099_);
                    v___x_5101_ = v_reuseFailAlloc_5102_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5101_;
            }
            21 => {
                return v___x_5115_;
            }
            22 => {
                return v___x_5118_;
            }
            23 => {
                return v___x_5134_;
            }
            24 => {
                v_size_5139_ = leanh::lean_ctor_get(v_l_5126_, 0);
                v_k_5140_ = leanh::lean_ctor_get(v_l_5126_, 1);
                v_v_5141_ = leanh::lean_ctor_get(v_l_5126_, 2);
                v_l_5142_ = leanh::lean_ctor_get(v_l_5126_, 3);
                v_r_5143_ = leanh::lean_ctor_get(v_l_5126_, 4);
                v_size_5144_ = leanh::lean_ctor_get(v_r_5127_, 0);
                v___x_5145_ = leanh::lean_unsigned_to_nat(2);
                v___x_5146_ = lean_nat_mul(v___x_5145_, v_size_5144_);
                v___x_5147_ = lean_nat_dec_lt(v_size_5139_, v___x_5146_);
                leanh::lean_dec(v___x_5146_);
                if v___x_5147_ == 0 {
                    leanh::lean_inc(v_r_5143_);
                    leanh::lean_inc(v_l_5142_);
                    leanh::lean_inc(v_v_5141_);
                    leanh::lean_inc(v_k_5140_);
                    v_isSharedCheck_5175_ = (!leanh::lean_is_exclusive(v_l_5126_)) as u8;
                    if v_isSharedCheck_5175_ == 0 {
                        v_unused_5176_ = leanh::lean_ctor_get(v_l_5126_, 4);
                        leanh::lean_dec(v_unused_5176_);
                        v_unused_5177_ = leanh::lean_ctor_get(v_l_5126_, 3);
                        leanh::lean_dec(v_unused_5177_);
                        v_unused_5178_ = leanh::lean_ctor_get(v_l_5126_, 2);
                        leanh::lean_dec(v_unused_5178_);
                        v_unused_5179_ = leanh::lean_ctor_get(v_l_5126_, 1);
                        leanh::lean_dec(v_unused_5179_);
                        v_unused_5180_ = leanh::lean_ctor_get(v_l_5126_, 0);
                        leanh::lean_dec(v_unused_5180_);
                        v___x_5149_ = v_l_5126_;
                        v_isShared_5150_ = v_isSharedCheck_5175_;
                        state = 25;
                        continue;
                    } else {
                        leanh::lean_dec(v_l_5126_);
                        v___x_5149_ = leanh::lean_box(0);
                        v_isShared_5150_ = v_isSharedCheck_5175_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4977_);
                    v___x_5181_ = lean_nat_add(v___x_5121_, v_size_5122_);
                    v___x_5182_ = lean_nat_add(v___x_5181_, v_size_5123_);
                    leanh::lean_dec(v_size_5123_);
                    v___x_5183_ = lean_nat_add(v___x_5181_, v_size_5139_);
                    leanh::lean_dec(v___x_5181_);
                    leanh::lean_inc_ref(v_l_4974_);
                    if v_isShared_5138_ == 0 {
                        leanh::lean_ctor_set(v___x_5137_, 4, v_l_5126_);
                        leanh::lean_ctor_set(v___x_5137_, 3, v_l_4974_);
                        leanh::lean_ctor_set(v___x_5137_, 2, v_v_4973_);
                        leanh::lean_ctor_set(v___x_5137_, 1, v_k_4972_);
                        leanh::lean_ctor_set(v___x_5137_, 0, v___x_5183_);
                        v___x_5185_ = v___x_5137_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5198_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 0, v___x_5183_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 1, v_k_4972_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 2, v_v_4973_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 3, v_l_4974_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 4, v_l_5126_);
                        v___x_5185_ = v_reuseFailAlloc_5198_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_5151_ = lean_nat_add(v___x_5121_, v_size_5122_);
                v___x_5152_ = lean_nat_add(v___x_5151_, v_size_5123_);
                leanh::lean_dec(v_size_5123_);
                if leanh::lean_obj_tag(v_l_5142_) == 0 {
                    v_size_5173_ = leanh::lean_ctor_get(v_l_5142_, 0);
                    leanh::lean_inc(v_size_5173_);
                    v___y_5165_ = v_size_5173_;
                    state = 29;
                    continue;
                } else {
                    v___x_5174_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5165_ = v___x_5174_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_5157_ = lean_nat_add(v___y_5154_, v___y_5156_);
                leanh::lean_dec(v___y_5156_);
                leanh::lean_dec(v___y_5154_);
                if v_isShared_5150_ == 0 {
                    leanh::lean_ctor_set(v___x_5149_, 4, v_r_5127_);
                    leanh::lean_ctor_set(v___x_5149_, 3, v_r_5143_);
                    leanh::lean_ctor_set(v___x_5149_, 2, v_v_5125_);
                    leanh::lean_ctor_set(v___x_5149_, 1, v_k_5124_);
                    leanh::lean_ctor_set(v___x_5149_, 0, v___x_5157_);
                    v___x_5159_ = v___x_5149_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_k_5124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 2, v_v_5125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 3, v_r_5143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 4, v_r_5127_);
                    v___x_5159_ = v_reuseFailAlloc_5163_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5138_ == 0 {
                    leanh::lean_ctor_set(v___x_5137_, 4, v___x_5159_);
                    leanh::lean_ctor_set(v___x_5137_, 3, v___y_5155_);
                    leanh::lean_ctor_set(v___x_5137_, 2, v_v_5141_);
                    leanh::lean_ctor_set(v___x_5137_, 1, v_k_5140_);
                    leanh::lean_ctor_set(v___x_5137_, 0, v___x_5152_);
                    v___x_5161_ = v___x_5137_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5162_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_k_5140_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 2, v_v_5141_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 3, v___y_5155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 4, v___x_5159_);
                    v___x_5161_ = v_reuseFailAlloc_5162_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5161_;
            }
            29 => {
                v___x_5166_ = lean_nat_add(v___x_5151_, v___y_5165_);
                leanh::lean_dec(v___y_5165_);
                leanh::lean_dec(v___x_5151_);
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v_l_5142_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5166_);
                    v___x_5168_ = v___x_4977_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 3, v_l_4974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 4, v_l_5142_);
                    v___x_5168_ = v_reuseFailAlloc_5172_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_5169_ = lean_nat_add(v___x_5121_, v_size_5144_);
                if leanh::lean_obj_tag(v_r_5143_) == 0 {
                    v_size_5170_ = leanh::lean_ctor_get(v_r_5143_, 0);
                    leanh::lean_inc(v_size_5170_);
                    v___y_5154_ = v___x_5169_;
                    v___y_5155_ = v___x_5168_;
                    v___y_5156_ = v_size_5170_;
                    state = 26;
                    continue;
                } else {
                    v___x_5171_ = leanh::lean_unsigned_to_nat(0);
                    v___y_5154_ = v___x_5169_;
                    v___y_5155_ = v___x_5168_;
                    v___y_5156_ = v___x_5171_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_5192_ = (!leanh::lean_is_exclusive(v_l_4974_)) as u8;
                if v_isSharedCheck_5192_ == 0 {
                    v_unused_5193_ = leanh::lean_ctor_get(v_l_4974_, 4);
                    leanh::lean_dec(v_unused_5193_);
                    v_unused_5194_ = leanh::lean_ctor_get(v_l_4974_, 3);
                    leanh::lean_dec(v_unused_5194_);
                    v_unused_5195_ = leanh::lean_ctor_get(v_l_4974_, 2);
                    leanh::lean_dec(v_unused_5195_);
                    v_unused_5196_ = leanh::lean_ctor_get(v_l_4974_, 1);
                    leanh::lean_dec(v_unused_5196_);
                    v_unused_5197_ = leanh::lean_ctor_get(v_l_4974_, 0);
                    leanh::lean_dec(v_unused_5197_);
                    v___x_5187_ = v_l_4974_;
                    v_isShared_5188_ = v_isSharedCheck_5192_;
                    state = 32;
                    continue;
                } else {
                    leanh::lean_dec(v_l_4974_);
                    v___x_5187_ = leanh::lean_box(0);
                    v_isShared_5188_ = v_isSharedCheck_5192_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_5188_ == 0 {
                    leanh::lean_ctor_set(v___x_5187_, 4, v_r_5127_);
                    leanh::lean_ctor_set(v___x_5187_, 3, v___x_5185_);
                    leanh::lean_ctor_set(v___x_5187_, 2, v_v_5125_);
                    leanh::lean_ctor_set(v___x_5187_, 1, v_k_5124_);
                    leanh::lean_ctor_set(v___x_5187_, 0, v___x_5182_);
                    v___x_5190_ = v___x_5187_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5182_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_k_5124_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_v_5125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 3, v___x_5185_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_r_5127_);
                    v___x_5190_ = v_reuseFailAlloc_5191_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5190_;
            }
            34 => {
                v_k_5212_ = leanh::lean_ctor_get(v_l_5205_, 1);
                v_v_5213_ = leanh::lean_ctor_get(v_l_5205_, 2);
                v_isSharedCheck_5227_ = (!leanh::lean_is_exclusive(v_l_5205_)) as u8;
                if v_isSharedCheck_5227_ == 0 {
                    v_unused_5228_ = leanh::lean_ctor_get(v_l_5205_, 4);
                    leanh::lean_dec(v_unused_5228_);
                    v_unused_5229_ = leanh::lean_ctor_get(v_l_5205_, 3);
                    leanh::lean_dec(v_unused_5229_);
                    v_unused_5230_ = leanh::lean_ctor_get(v_l_5205_, 0);
                    leanh::lean_dec(v_unused_5230_);
                    v___x_5215_ = v_l_5205_;
                    v_isShared_5216_ = v_isSharedCheck_5227_;
                    state = 35;
                    continue;
                } else {
                    leanh::lean_inc(v_v_5213_);
                    leanh::lean_inc(v_k_5212_);
                    leanh::lean_dec(v_l_5205_);
                    v___x_5215_ = leanh::lean_box(0);
                    v_isShared_5216_ = v_isSharedCheck_5227_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_5217_ = leanh::lean_unsigned_to_nat(3);
                leanh::lean_inc_n(v_r_5206_, 2);
                if v_isShared_5216_ == 0 {
                    leanh::lean_ctor_set(v___x_5215_, 4, v_r_5206_);
                    leanh::lean_ctor_set(v___x_5215_, 3, v_r_5206_);
                    leanh::lean_ctor_set(v___x_5215_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v___x_5215_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v___x_5215_, 0, v___x_5121_);
                    v___x_5219_ = v___x_5215_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5226_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 3, v_r_5206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 4, v_r_5206_);
                    v___x_5219_ = v_reuseFailAlloc_5226_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                leanh::lean_inc(v_r_5206_);
                if v_isShared_5211_ == 0 {
                    leanh::lean_ctor_set(v___x_5210_, 3, v_r_5206_);
                    leanh::lean_ctor_set(v___x_5210_, 0, v___x_5121_);
                    v___x_5221_ = v___x_5210_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5225_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 1, v_k_5207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 2, v_v_5208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 3, v_r_5206_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 4, v_r_5206_);
                    v___x_5221_ = v_reuseFailAlloc_5225_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v___x_5221_);
                    leanh::lean_ctor_set(v___x_4977_, 3, v___x_5219_);
                    leanh::lean_ctor_set(v___x_4977_, 2, v_v_5213_);
                    leanh::lean_ctor_set(v___x_4977_, 1, v_k_5212_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5217_);
                    v___x_5223_ = v___x_4977_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_k_5212_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 2, v_v_5213_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 3, v___x_5219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 4, v___x_5221_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5223_;
            }
            39 => {
                v___x_5240_ = leanh::lean_unsigned_to_nat(3);
                if v_isShared_5239_ == 0 {
                    leanh::lean_ctor_set(v___x_5238_, 4, v_l_5205_);
                    leanh::lean_ctor_set(v___x_5238_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v___x_5238_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v___x_5238_, 0, v___x_5121_);
                    v___x_5242_ = v___x_5238_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5121_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_k_4972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_v_4973_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_l_5205_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 4, v_l_5205_);
                    v___x_5242_ = v_reuseFailAlloc_5246_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4978_ == 0 {
                    leanh::lean_ctor_set(v___x_4977_, 4, v_r_5234_);
                    leanh::lean_ctor_set(v___x_4977_, 3, v___x_5242_);
                    leanh::lean_ctor_set(v___x_4977_, 2, v_v_5236_);
                    leanh::lean_ctor_set(v___x_4977_, 1, v_k_5235_);
                    leanh::lean_ctor_set(v___x_4977_, 0, v___x_5240_);
                    v___x_5244_ = v___x_4977_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_k_5235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 2, v_v_5236_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 3, v___x_5242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 4, v_r_5234_);
                    v___x_5244_ = v_reuseFailAlloc_5245_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5244_;
            }
            42 => {
                return v___x_5253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(
    mut v_k_5258_: *mut leanh::LeanObject,
    mut v_t_5259_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_5259_) == 0 {
                    v_k_5260_ = leanh::lean_ctor_get(v_t_5259_, 1);
                    v_l_5261_ = leanh::lean_ctor_get(v_t_5259_, 3);
                    v_r_5262_ = leanh::lean_ctor_get(v_t_5259_, 4);
                    v___x_5263_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_5258_, v_k_5260_);
                    match v___x_5263_ {
                        0 => {
                            v_t_5259_ = v_l_5261_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_5265_ = 1;
                            return v___x_5265_;
                        }
                        _ => {
                            v_t_5259_ = v_r_5262_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_5267_ = 0;
                    return v___x_5267_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg___boxed(
    mut v_k_5268_: *mut leanh::LeanObject,
    mut v_t_5269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5270_: u8 = 0;
    let mut v_r_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(
            v_k_5268_, v_t_5269_,
        );
    leanh::lean_dec(v_t_5269_);
    leanh::lean_dec(v_k_5268_);
    v_r_5271_ = leanh::lean_box((v_res_5270_) as usize);
    return v_r_5271_;
}
pub unsafe fn l_Lean_Level_collectMVars(
    mut v_u_5272_: *mut leanh::LeanObject,
    mut v_s_5273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_5275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_u_5272_) {
                1 => {
                    v_a_5279_ = leanh::lean_ctor_get(v_u_5272_, 0);
                    leanh::lean_inc(v_a_5279_);
                    leanh::lean_dec_ref_known(v_u_5272_, 1);
                    v_u_5272_ = v_a_5279_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_a_5281_ = leanh::lean_ctor_get(v_u_5272_, 0);
                    leanh::lean_inc(v_a_5281_);
                    v_a_5282_ = leanh::lean_ctor_get(v_u_5272_, 1);
                    leanh::lean_inc(v_a_5282_);
                    leanh::lean_dec_ref_known(v_u_5272_, 2);
                    v_u_5275_ = v_a_5281_;
                    v_v_5276_ = v_a_5282_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_5283_ = leanh::lean_ctor_get(v_u_5272_, 0);
                    leanh::lean_inc(v_a_5283_);
                    v_a_5284_ = leanh::lean_ctor_get(v_u_5272_, 1);
                    leanh::lean_inc(v_a_5284_);
                    leanh::lean_dec_ref_known(v_u_5272_, 2);
                    v_u_5275_ = v_a_5283_;
                    v_v_5276_ = v_a_5284_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_a_5285_ = leanh::lean_ctor_get(v_u_5272_, 0);
                    leanh::lean_inc(v_a_5285_);
                    leanh::lean_dec_ref_known(v_u_5272_, 1);
                    v___x_5286_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_5285_, v_s_5273_);
                    if v___x_5286_ == 0 {
                        v___x_5287_ = leanh::lean_box(0);
                        v___x_5288_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_5285_, v___x_5287_, v_s_5273_);
                        return v___x_5288_;
                    } else {
                        leanh::lean_dec(v_a_5285_);
                        return v_s_5273_;
                    }
                }
                _ => {
                    leanh::lean_dec(v_u_5272_);
                    return v_s_5273_;
                }
            },
            1 => {
                v___x_5277_ = l_Lean_Level_collectMVars(v_v_5276_, v_s_5273_);
                v_u_5272_ = v_u_5275_;
                v_s_5273_ = v___x_5277_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(
    mut v_00_u03b2_5289_: *mut leanh::LeanObject,
    mut v_k_5290_: *mut leanh::LeanObject,
    mut v_t_5291_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5292_: u8 = 0;
    v___x_5292_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(
            v_k_5290_, v_t_5291_,
        );
    return v___x_5292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(
    mut v_00_u03b2_5293_: *mut leanh::LeanObject,
    mut v_k_5294_: *mut leanh::LeanObject,
    mut v_t_5295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5296_: u8 = 0;
    let mut v_r_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(
        v_00_u03b2_5293_,
        v_k_5294_,
        v_t_5295_,
    );
    leanh::lean_dec(v_t_5295_);
    leanh::lean_dec(v_k_5294_);
    v_r_5297_ = leanh::lean_box((v_res_5296_) as usize);
    return v_r_5297_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(
    mut v_00_u03b2_5298_: *mut leanh::LeanObject,
    mut v_k_5299_: *mut leanh::LeanObject,
    mut v_v_5300_: *mut leanh::LeanObject,
    mut v_t_5301_: *mut leanh::LeanObject,
    mut v_hl_5302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5303_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(
            v_k_5299_, v_v_5300_, v_t_5301_,
        );
    return v___x_5303_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_find_x3f_visit(
    mut v_p_5304_: *mut leanh::LeanObject,
    mut v_u_5305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    let mut v_a_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_p_5304_);
                leanh::lean_inc(v_u_5305_);
                v___x_5311_ = leanh::lean_apply_1(v_p_5304_, v_u_5305_);
                v___x_5312_ = (leanh::lean_unbox(v___x_5311_) as u8);
                if v___x_5312_ == 0 {
                    match leanh::lean_obj_tag(v_u_5305_) {
                        1 => {
                            v_a_5313_ = leanh::lean_ctor_get(v_u_5305_, 0);
                            leanh::lean_inc(v_a_5313_);
                            leanh::lean_dec_ref_known(v_u_5305_, 1);
                            v_u_5305_ = v_a_5313_;
                            state = 0;
                            continue;
                        }
                        2 => {
                            v_a_5315_ = leanh::lean_ctor_get(v_u_5305_, 0);
                            leanh::lean_inc(v_a_5315_);
                            v_a_5316_ = leanh::lean_ctor_get(v_u_5305_, 1);
                            leanh::lean_inc(v_a_5316_);
                            leanh::lean_dec_ref_known(v_u_5305_, 2);
                            v_u_5307_ = v_a_5315_;
                            v_v_5308_ = v_a_5316_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_a_5317_ = leanh::lean_ctor_get(v_u_5305_, 0);
                            leanh::lean_inc(v_a_5317_);
                            v_a_5318_ = leanh::lean_ctor_get(v_u_5305_, 1);
                            leanh::lean_inc(v_a_5318_);
                            leanh::lean_dec_ref_known(v_u_5305_, 2);
                            v_u_5307_ = v_a_5317_;
                            v_v_5308_ = v_a_5318_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            leanh::lean_dec(v_u_5305_);
                            leanh::lean_dec_ref(v_p_5304_);
                            v___x_5319_ = leanh::lean_box(0);
                            return v___x_5319_;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_p_5304_);
                    v___x_5320_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5320_, 0, v_u_5305_);
                    return v___x_5320_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_p_5304_);
                v___x_5309_ =
                    l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5304_, v_u_5307_);
                if leanh::lean_obj_tag(v___x_5309_) == 0 {
                    v_u_5305_ = v_v_5308_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_v_5308_);
                    leanh::lean_dec_ref(v_p_5304_);
                    return v___x_5309_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_find_x3f(
    mut v_u_5321_: *mut leanh::LeanObject,
    mut v_p_5322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5323_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5322_, v_u_5321_);
    return v___x_5323_;
}
pub unsafe fn l_Lean_Level_any(
    mut v_u_5324_: *mut leanh::LeanObject,
    mut v_p_5325_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5325_, v_u_5324_);
    if leanh::lean_obj_tag(v___x_5326_) == 0 {
        let mut v___x_5327_: u8 = 0;
        v___x_5327_ = 0;
        return v___x_5327_;
    } else {
        let mut v___x_5328_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_5326_, 1);
        v___x_5328_ = 1;
        return v___x_5328_;
    }
}
pub unsafe fn l_Lean_Level_any___boxed(
    mut v_u_5329_: *mut leanh::LeanObject,
    mut v_p_5330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5331_: u8 = 0;
    let mut v_r_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5331_ = l_Lean_Level_any(v_u_5329_, v_p_5330_);
    v_r_5332_ = leanh::lean_box((v_res_5331_) as usize);
    return v_r_5332_;
}
pub unsafe fn l_Nat_toLevel(
    mut v_n_5333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5334_ = l_Lean_Level_ofNat(v_n_5333_);
    return v___x_5334_;
}
pub unsafe fn l_Nat_toLevel___boxed(
    mut v_n_5335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5336_ = l_Nat_toLevel(v_n_5335_);
    leanh::lean_dec(v_n_5335_);
    return v_res_5336_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Level(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_QSort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Hygiene(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedData___aux__1 = _init_l_Lean_instInhabitedData___aux__1();
    l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
    l_Lean_instInhabitedLevelMVarId_default = _init_l_Lean_instInhabitedLevelMVarId_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLevelMVarId_default);
    l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
    l_Lean_instInhabitedLMVarIdSet___aux__1 = _init_l_Lean_instInhabitedLMVarIdSet___aux__1();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet___aux__1);
    l_Lean_instInhabitedLMVarIdSet = _init_l_Lean_instInhabitedLMVarIdSet();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet);
    l_Lean_instEmptyCollectionLMVarIdSet___aux__1 =
        _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1();
    leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet___aux__1);
    l_Lean_instEmptyCollectionLMVarIdSet = _init_l_Lean_instEmptyCollectionLMVarIdSet();
    leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet);
    l_Lean_Level_zero___override = _init_l_Lean_Level_zero___override();
    leanh::lean_mark_persistent(l_Lean_Level_zero___override);
    l_Lean_instInhabitedLevel_default = _init_l_Lean_instInhabitedLevel_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLevel_default);
    l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
    leanh::lean_mark_persistent(l_Lean_instInhabitedLevel);
    l_Lean_levelZero = _init_l_Lean_levelZero();
    leanh::lean_mark_persistent(l_Lean_levelZero);
    l_Lean_Level_one = _init_l_Lean_Level_one();
    leanh::lean_mark_persistent(l_Lean_Level_one);
    l_Lean_levelOne = _init_l_Lean_levelOne();
    leanh::lean_mark_persistent(l_Lean_levelOne);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Level(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Level(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_QSort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashSet(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Hygiene(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Level(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Level(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Level(builtin);
}