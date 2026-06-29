// Lean compiler output
// Module: Lean.Level
// Imports: Init.Data.Array.QSort Lean.Data.PersistentHashSet Lean.Hygiene Init.Data.Option.Coe Init.Data.Nat.Linear
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{lean_uint64_land, lean_uint64_shift_right};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_to_uint64, lean_uint64_to_nat, lean_uint64_to_uint32, lean_usize_add,
    lean_usize_dec_lt,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub, lean_panic_fn_borrowed, lean_uint32_dec_eq,
    lean_uint32_to_nat, lean_uint64_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Level::{lean_level_eq, lean_level_mk_data};
static mut l_Lean_instInhabitedData___aux__1___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedData___aux__1___closed__0: u64 = 0;
pub static mut l_Lean_instInhabitedData___aux__1: u64 = 0;
pub static mut l_Lean_instInhabitedData: u64 = 0;
pub static l_Lean_instBEqData___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_UInt64_decEq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqData___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqData: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqData___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__1_value: crate::leanh::LeanStringObject<15> =
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
            32, 40, 104, 97, 115, 80, 97, 114, 97, 109, 32, 58, 61, 32, 0,
        ],
    };
static mut l_Lean_instReprData___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__4_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__5_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprData___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprData___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprData___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprData___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprData: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprData___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLevelMVarId_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLevelMVarId: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqLevelMVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqLevelMVarId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqLevelMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instBEqLevelMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instHashableLevelMVarId_hash___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableLevelMVarId_hash___closed__0: u64 = 0;
static mut l_Lean_instHashableLevelMVarId_hash___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableLevelMVarId_hash___closed__1: u64 = 0;
pub static l_Lean_instHashableLevelMVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableLevelMVarId_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableLevelMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instHashableLevelMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_instReprLevelMVarId_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevelMVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLevelMVarId_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLevelMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLevelMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevelMVarId___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLMVarId___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_reprPrec___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLMVarId___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLMVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLMVarId: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLMVarId___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedLMVarIdSet___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLMVarIdSet: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instEmptyCollectionLMVarIdSet___aux__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instEmptyCollectionLMVarIdSet: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Level_zero___override: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Level_data___override___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_data___override___closed__0: u64 = 0;
pub static mut l_Lean_instInhabitedLevel_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedLevel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprLevel_repr___closed__0_value: crate::leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 122, 101, 114, 111, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_instReprLevel_repr___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevel_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprLevel_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprLevel_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprLevel_repr___closed__4_value: crate::leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 115, 117, 99, 99, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__6_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__7_value: crate::leanh::LeanStringObject<15> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__8_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__10_value: crate::leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 105, 109, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__11_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__10_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__12_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__11_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__13_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 112, 97, 114, 97, 109, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__14_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__13_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__16_value: crate::leanh::LeanStringObject<16> =
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
            76, 101, 97, 110, 46, 76, 101, 118, 101, 108, 46, 109, 118, 97, 114, 0,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__17_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__16_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel_repr___closed__18_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__17_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprLevel_repr___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel_repr___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instReprLevel___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprLevel_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprLevel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instReprLevel: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprLevel___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Level_instHashable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_levelZero: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Level_one___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_one___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Level_one: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_levelOne: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Level_mvarId_x21___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_mvarId_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_mvarId_x21___closed__1_value: crate::leanh::LeanStringObject<19> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_mvarId_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_mvarId_x21___closed__2_value: crate::leanh::LeanStringObject<22> =
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
            109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 101, 120, 112, 101, 99,
            116, 101, 100, 0,
        ],
    };
static mut l_Lean_Level_mvarId_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_mvarId_x21___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_mvarId_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_mvarId_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_instBEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Level_instBEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Level_normalize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_normalize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_normalize___closed__1_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_normalize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_normalize___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_normalize___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_normalize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_toResult___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Level_PP_toResult___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_toResult___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13286986945483979944 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_toResult___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__4_value)
                as *mut crate::leanh::LeanObject,
            13784598040954107364 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__6_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_toResult___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__7_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__6_value)
                as *mut crate::leanh::LeanObject,
            3978731030111751661 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_toResult___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_toResult___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__8_value)
                as *mut crate::leanh::LeanObject,
            601732279143319601 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_toResult___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_toResult___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value:
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
    m_data: [40, 0],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprData___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_format___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__2_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_format___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__4_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_format___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_format___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_format___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__4_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__3_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11423656342444823216 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__5_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__4_value)
                as *mut crate::leanh::LeanObject,
            16533827001853265987 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Level_PP_Result_quote___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__8_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11423656342444823216 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__8_value)
                as *mut crate::leanh::LeanObject,
            12560806670959244085 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__10_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__11_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11423656342444823216 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__11_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__2_value)
                as *mut crate::leanh::LeanObject,
            7017890982578468202 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_PP_Result_quote___closed__13_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Level_PP_Result_quote___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_PP_Result_quote___closed__14_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__13_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Level_PP_Result_quote___closed__16_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__3_value)
                as *mut crate::leanh::LeanObject,
            11423656342444823216 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Level_PP_Result_quote___closed__16_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Level_PP_Result_format___closed__4_value)
                as *mut crate::leanh::LeanObject,
            2051294913818044796 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_PP_Result_quote___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_PP_Result_quote___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Level_PP_Result_quote___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Level_PP_Result_quote___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Level_instToFormat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Level_instToFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Level_instToFormat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_instToFormat___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Level_instToFormat___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instToFormat___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Level_instToFormat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_instToString___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Level_instToString___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Level_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Level_instQuoteMkStr1___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Level_instQuoteMkStr1___lam__1 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Level_instToFormat___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Level_instQuoteMkStr1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instQuoteMkStr1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Level_instQuoteMkStr1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Level_instQuoteMkStr1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value:
    crate::leanh::LeanStringObject<49> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Nat_imax(
    mut v_n_2669_: *mut crate::leanh::LeanObject,
    mut v_m_2670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: u8 = 0;
    v___x_2671_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2672_ = lean_nat_dec_eq(v_m_2670_, v___x_2671_);
    if v___x_2672_ == 0 {
        let mut v___x_2673_: u8 = 0;
        v___x_2673_ = lean_nat_dec_le(v_n_2669_, v_m_2670_);
        if v___x_2673_ == 0 {
            crate::leanh::lean_inc(v_n_2669_);
            return v_n_2669_;
        } else {
            crate::leanh::lean_inc(v_m_2670_);
            return v_m_2670_;
        }
    } else {
        return v___x_2671_;
    }
}
pub unsafe fn l_Nat_imax___boxed(
    mut v_n_2674_: *mut crate::leanh::LeanObject,
    mut v_m_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Nat_imax(v_n_2674_, v_m_2675_);
    crate::leanh::lean_dec(v_m_2675_);
    crate::leanh::lean_dec(v_n_2674_);
    return v_res_2676_;
}
pub unsafe fn _init_l_Lean_instInhabitedData___aux__1___closed__0() -> u64 {
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u64 = 0;
    v___x_2677_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2678_ = lean_uint64_of_nat(v___x_2677_);
    return v___x_2678_;
}
pub unsafe fn _init_l_Lean_instInhabitedData___aux__1() -> u64 {
    let mut v___x_2679_: u64 = 0;
    v___x_2679_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedData___aux__1___closed__0_once),
        _init_l_Lean_instInhabitedData___aux__1___closed__0,
    );
    return v___x_2679_;
}
pub unsafe fn _init_l_Lean_instInhabitedData() -> u64 {
    let mut v___x_2680_: u64 = 0;
    v___x_2680_ = crate::leanh::lean_uint64_once(
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
    mut v_c_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2685_: u64 = 0;
    let mut v_res_2686_: u64 = 0;
    let mut v_r_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2685_ = crate::leanh::lean_unbox_uint64(v_c_2684_);
    crate::leanh::lean_dec_ref(v_c_2684_);
    v_res_2686_ = l_Lean_Level_Data_hash(v_c_boxed_2685_);
    v_r_2687_ = crate::leanh::lean_box_uint64(v_res_2686_);
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
    mut v_c_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2695_: u64 = 0;
    let mut v_res_2696_: u32 = 0;
    let mut v_r_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2695_ = crate::leanh::lean_unbox_uint64(v_c_2694_);
    crate::leanh::lean_dec_ref(v_c_2694_);
    v_res_2696_ = l_Lean_Level_Data_depth(v_c_boxed_2695_);
    v_r_2697_ = crate::leanh::lean_box_uint32(v_res_2696_);
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
    mut v_c_2704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2705_: u64 = 0;
    let mut v_res_2706_: u8 = 0;
    let mut v_r_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2705_ = crate::leanh::lean_unbox_uint64(v_c_2704_);
    crate::leanh::lean_dec_ref(v_c_2704_);
    v_res_2706_ = l_Lean_Level_Data_hasMVar(v_c_boxed_2705_);
    v_r_2707_ = crate::leanh::lean_box((v_res_2706_) as usize);
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
    mut v_c_2714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_2715_: u64 = 0;
    let mut v_res_2716_: u8 = 0;
    let mut v_r_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2715_ = crate::leanh::lean_unbox_uint64(v_c_2714_);
    crate::leanh::lean_dec_ref(v_c_2714_);
    v_res_2716_ = l_Lean_Level_Data_hasParam(v_c_boxed_2715_);
    v_r_2717_ = crate::leanh::lean_box((v_res_2716_) as usize);
    return v_r_2717_;
}
pub unsafe fn l_Lean_Level_mkData___boxed(
    mut v_h_2722_: *mut crate::leanh::LeanObject,
    mut v_depth_2723_: *mut crate::leanh::LeanObject,
    mut v_hasMVar_2724_: *mut crate::leanh::LeanObject,
    mut v_hasParam_2725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_h_boxed_2726_: u64 = 0;
    let mut v_hasMVar_boxed_2727_: u8 = 0;
    let mut v_hasParam_boxed_2728_: u8 = 0;
    let mut v_res_2729_: u64 = 0;
    let mut v_r_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_h_boxed_2726_ = crate::leanh::lean_unbox_uint64(v_h_2722_);
    crate::leanh::lean_dec_ref(v_h_2722_);
    v_hasMVar_boxed_2727_ = (crate::leanh::lean_unbox(v_hasMVar_2724_) as u8);
    v_hasParam_boxed_2728_ = (crate::leanh::lean_unbox(v_hasParam_2725_) as u8);
    v_res_2729_ = lean_level_mk_data(
        v_h_boxed_2726_,
        v_depth_2723_,
        v_hasMVar_boxed_2727_,
        v_hasParam_boxed_2728_,
    );
    v_r_2730_ = crate::leanh::lean_box_uint64(v_res_2729_);
    return v_r_2730_;
}
pub unsafe fn l_Lean_instReprData___lam__0(
    mut v_v_2738_: u64,
    mut v_prec_2739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u64 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: u32 = 0;
    let mut v___x_2776_: u32 = 0;
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2770_ = l_Lean_instReprData___lam__0___closed__5;
                v___x_2771_ = l_Lean_Level_Data_hash(v_v_2738_);
                v___x_2772_ = lean_uint64_to_nat(v___x_2771_);
                v___x_2773_ = l_Nat_reprFast(v___x_2772_);
                v_r_2774_ = lean_string_append(v___x_2770_, v___x_2773_);
                crate::leanh::lean_dec_ref(v___x_2773_);
                v___x_2775_ = l_Lean_Level_Data_depth(v_v_2738_);
                v___x_2776_ = 0;
                v___x_2777_ = lean_uint32_dec_eq(v___x_2775_, v___x_2776_);
                if v___x_2777_ == 0 {
                    v___x_2778_ = l_Lean_instReprData___lam__0___closed__6;
                    v___x_2779_ = lean_string_append(v_r_2774_, v___x_2778_);
                    v___x_2780_ = lean_uint32_to_nat(v___x_2775_);
                    v___x_2781_ = l_Nat_reprFast(v___x_2780_);
                    v___x_2782_ = lean_string_append(v___x_2779_, v___x_2781_);
                    crate::leanh::lean_dec_ref(v___x_2781_);
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
                v___x_2742_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2742_, 0, v_r_2741_);
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
    mut v_v_2785_: *mut crate::leanh::LeanObject,
    mut v_prec_2786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_boxed_2787_: u64 = 0;
    let mut v_res_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_2787_ = crate::leanh::lean_unbox_uint64(v_v_2785_);
    crate::leanh::lean_dec_ref(v_v_2785_);
    v_res_2788_ = l_Lean_instReprData___lam__0(v_v_boxed_2787_, v_prec_2786_);
    crate::leanh::lean_dec(v_prec_2786_);
    return v_res_2788_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevelMVarId_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2791_ = crate::leanh::lean_box(0);
    return v___x_2791_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevelMVarId() -> *mut crate::leanh::LeanObject {
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2792_ = crate::leanh::lean_box(0);
    return v___x_2792_;
}
pub unsafe fn l_Lean_instBEqLevelMVarId_beq(
    mut v_x_2793_: *mut crate::leanh::LeanObject,
    mut v_x_2794_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2795_: u8 = 0;
    v___x_2795_ = lean_name_eq(v_x_2793_, v_x_2794_);
    return v___x_2795_;
}
pub unsafe fn l_Lean_instBEqLevelMVarId_beq___boxed(
    mut v_x_2796_: *mut crate::leanh::LeanObject,
    mut v_x_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2798_: u8 = 0;
    let mut v_r_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2798_ = l_Lean_instBEqLevelMVarId_beq(v_x_2796_, v_x_2797_);
    crate::leanh::lean_dec(v_x_2797_);
    crate::leanh::lean_dec(v_x_2796_);
    v_r_2799_ = crate::leanh::lean_box((v_res_2798_) as usize);
    return v_r_2799_;
}
pub unsafe fn _init_l_Lean_instHashableLevelMVarId_hash___closed__0() -> u64 {
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: u64 = 0;
    v___x_2802_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2803_ = lean_uint64_of_nat(v___x_2802_);
    return v___x_2803_;
}
pub unsafe fn _init_l_Lean_instHashableLevelMVarId_hash___closed__1() -> u64 {
    let mut v___x_2804_: u64 = 0;
    let mut v___x_2805_: u64 = 0;
    let mut v___x_2806_: u64 = 0;
    v___x_2804_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__0_once),
        _init_l_Lean_instHashableLevelMVarId_hash___closed__0,
    );
    v___x_2805_ = 0u64;
    v___x_2806_ = lean_uint64_mix_hash(v___x_2805_, v___x_2804_);
    return v___x_2806_;
}
pub unsafe fn l_Lean_instHashableLevelMVarId_hash(
    mut v_x_2807_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_2808_: u64 = 0;
    v___x_2808_ = 0u64;
    if crate::leanh::lean_obj_tag(v_x_2807_) == 0 {
        let mut v___x_2809_: u64 = 0;
        v___x_2809_ = crate::leanh::lean_uint64_once(
            core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__1),
            core::ptr::addr_of_mut!(l_Lean_instHashableLevelMVarId_hash___closed__1_once),
            _init_l_Lean_instHashableLevelMVarId_hash___closed__1,
        );
        return v___x_2809_;
    } else {
        let mut v_hash_2810_: u64 = 0;
        let mut v___x_2811_: u64 = 0;
        v_hash_2810_ = crate::leanh::lean_ctor_get_uint64(
            v_x_2807_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
        );
        v___x_2811_ = lean_uint64_mix_hash(v___x_2808_, v_hash_2810_);
        return v___x_2811_;
    }
}
pub unsafe fn l_Lean_instHashableLevelMVarId_hash___boxed(
    mut v_x_2812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2813_: u64 = 0;
    let mut v_r_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2813_ = l_Lean_instHashableLevelMVarId_hash(v_x_2812_);
    crate::leanh::lean_dec(v_x_2812_);
    v_r_2814_ = crate::leanh::lean_box_uint64(v_res_2813_);
    return v_r_2814_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprLevelMVarId_repr_spec__0(
    mut v_a_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2818_ = lean_nat_to_int(v_a_2817_);
    return v___x_2818_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2832_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_2833_ = lean_nat_to_int(v___x_2832_);
    return v___x_2833_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2835_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__0;
    v___x_2836_ = lean_string_length(v___x_2835_);
    return v___x_2836_;
}
pub unsafe fn _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2837_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__9_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__9,
    );
    v___x_2838_ = lean_nat_to_int(v___x_2837_);
    return v___x_2838_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr___redArg(
    mut v_x_2843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: u8 = 0;
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2844_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__6;
    v___x_2845_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__7_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__7,
    );
    v___x_2846_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2847_ = l_Lean_Name_reprPrec(v_x_2843_, v___x_2846_);
    v___x_2848_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2848_, 0, v___x_2845_);
    crate::leanh::lean_ctor_set(v___x_2848_, 1, v___x_2847_);
    v___x_2849_ = 0;
    v___x_2850_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2850_, 0, v___x_2848_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2850_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2849_,
    );
    v___x_2851_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2851_, 0, v___x_2844_);
    crate::leanh::lean_ctor_set(v___x_2851_, 1, v___x_2850_);
    v___x_2852_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instReprLevelMVarId_repr___redArg___closed__10_once),
        _init_l_Lean_instReprLevelMVarId_repr___redArg___closed__10,
    );
    v___x_2853_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__11;
    v___x_2854_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2854_, 0, v___x_2853_);
    crate::leanh::lean_ctor_set(v___x_2854_, 1, v___x_2851_);
    v___x_2855_ = l_Lean_instReprLevelMVarId_repr___redArg___closed__12;
    v___x_2856_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2856_, 0, v___x_2854_);
    crate::leanh::lean_ctor_set(v___x_2856_, 1, v___x_2855_);
    v___x_2857_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2852_);
    crate::leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
    v___x_2858_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2858_, 0, v___x_2857_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2858_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2849_,
    );
    return v___x_2858_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr(
    mut v_x_2859_: *mut crate::leanh::LeanObject,
    mut v_prec_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2861_ = l_Lean_instReprLevelMVarId_repr___redArg(v_x_2859_);
    return v___x_2861_;
}
pub unsafe fn l_Lean_instReprLevelMVarId_repr___boxed(
    mut v_x_2862_: *mut crate::leanh::LeanObject,
    mut v_prec_2863_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_instReprLevelMVarId_repr(v_x_2862_, v_prec_2863_);
    crate::leanh::lean_dec(v_prec_2863_);
    return v_res_2864_;
}
pub unsafe fn _init_l_Lean_instInhabitedLMVarIdSet___aux__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2869_ = crate::leanh::lean_box(1);
    return v___x_2869_;
}
pub unsafe fn _init_l_Lean_instInhabitedLMVarIdSet() -> *mut crate::leanh::LeanObject {
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2870_ = crate::leanh::lean_box(1);
    return v___x_2870_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = crate::leanh::lean_box(1);
    return v___x_2871_;
}
pub unsafe fn _init_l_Lean_instEmptyCollectionLMVarIdSet() -> *mut crate::leanh::LeanObject {
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = crate::leanh::lean_box(1);
    return v___x_2872_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0(
    mut v_f_2873_: *mut crate::leanh::LeanObject,
    mut v_a_2874_: *mut crate::leanh::LeanObject,
    mut v_b_2875_: *mut crate::leanh::LeanObject,
    mut v_c_2876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2877_ = crate::leanh::lean_apply_2(v_f_2873_, v_a_2874_, v_c_2876_);
    return v___x_2877_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1(
    mut v_toPure_2878_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_2880_ = crate::leanh::lean_ctor_get(v_____do__lift_2879_, 0);
    crate::leanh::lean_inc(v_a_2880_);
    crate::leanh::lean_dec_ref(v_____do__lift_2879_);
    v___x_2881_ = crate::leanh::lean_apply_2(v_toPure_2878_, crate::leanh::lean_box(0), v_a_2880_);
    return v___x_2881_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg(
    mut v_inst_2882_: *mut crate::leanh::LeanObject,
    mut v_m_2883_: *mut crate::leanh::LeanObject,
    mut v_init_2884_: *mut crate::leanh::LeanObject,
    mut v_f_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2886_ = crate::leanh::lean_ctor_get(v_inst_2882_, 0);
    v_toBind_2887_ = crate::leanh::lean_ctor_get(v_inst_2882_, 1);
    crate::leanh::lean_inc(v_toBind_2887_);
    v_toPure_2888_ = crate::leanh::lean_ctor_get(v_toApplicative_2886_, 1);
    crate::leanh::lean_inc(v_toPure_2888_);
    v___f_2889_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2889_, 0, v_f_2885_);
    v___x_2890_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2882_,
        v___f_2889_,
        v_init_2884_,
        v_m_2883_,
    );
    v___f_2891_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2891_, 0, v_toPure_2888_);
    v___x_2892_ = crate::leanh::lean_apply_4(
        v_toBind_2887_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2890_,
        v___f_2891_,
    );
    return v___x_2892_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1(
    mut v_m_2893_: *mut crate::leanh::LeanObject,
    mut v_inst_2894_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2895_: *mut crate::leanh::LeanObject,
    mut v_m_2896_: *mut crate::leanh::LeanObject,
    mut v_init_2897_: *mut crate::leanh::LeanObject,
    mut v_f_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2899_ = crate::leanh::lean_ctor_get(v_inst_2894_, 0);
    v_toBind_2900_ = crate::leanh::lean_ctor_get(v_inst_2894_, 1);
    crate::leanh::lean_inc(v_toBind_2900_);
    v_toPure_2901_ = crate::leanh::lean_ctor_get(v_toApplicative_2899_, 1);
    crate::leanh::lean_inc(v_toPure_2901_);
    v___f_2902_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2902_, 0, v_f_2898_);
    v___x_2903_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2894_,
        v___f_2902_,
        v_init_2897_,
        v_m_2896_,
    );
    v___f_2904_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2904_, 0, v_toPure_2901_);
    v___x_2905_ = crate::leanh::lean_apply_4(
        v_toBind_2900_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2903_,
        v___f_2904_,
    );
    return v___x_2905_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad___redArg(
    mut v_inst_2906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2907_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2907_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2907_, 1, v_inst_2906_);
    return v___x_2907_;
}
pub unsafe fn l_Lean_instForInLMVarIdSetLMVarIdOfMonad(
    mut v_m_2908_: *mut crate::leanh::LeanObject,
    mut v_inst_2909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2910_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___x_2910_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2910_, 1, v_inst_2909_);
    return v___x_2910_;
}
pub unsafe fn l_Lean_instEmptyCollectionLMVarIdMap___aux__1(
    mut v_00_u03b1_2911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2912_ = crate::leanh::lean_box(1);
    return v___x_2912_;
}
pub unsafe fn l_Lean_instEmptyCollectionLMVarIdMap(
    mut v_00_u03b1_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ = crate::leanh::lean_box(1);
    return v___x_2914_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0(
    mut v_f_2915_: *mut crate::leanh::LeanObject,
    mut v_a_2916_: *mut crate::leanh::LeanObject,
    mut v_b_2917_: *mut crate::leanh::LeanObject,
    mut v_c_2918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2919_, 0, v_a_2916_);
    crate::leanh::lean_ctor_set(v___x_2919_, 1, v_b_2917_);
    v___x_2920_ = crate::leanh::lean_apply_2(v_f_2915_, v___x_2919_, v_c_2918_);
    return v___x_2920_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg(
    mut v_inst_2921_: *mut crate::leanh::LeanObject,
    mut v_m_2922_: *mut crate::leanh::LeanObject,
    mut v_init_2923_: *mut crate::leanh::LeanObject,
    mut v_f_2924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2925_ = crate::leanh::lean_ctor_get(v_inst_2921_, 0);
    v_toBind_2926_ = crate::leanh::lean_ctor_get(v_inst_2921_, 1);
    crate::leanh::lean_inc(v_toBind_2926_);
    v_toPure_2927_ = crate::leanh::lean_ctor_get(v_toApplicative_2925_, 1);
    crate::leanh::lean_inc(v_toPure_2927_);
    v___f_2928_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2928_, 0, v_f_2924_);
    v___x_2929_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2921_,
        v___f_2928_,
        v_init_2923_,
        v_m_2922_,
    );
    v___f_2930_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2930_, 0, v_toPure_2927_);
    v___x_2931_ = crate::leanh::lean_apply_4(
        v_toBind_2926_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2929_,
        v___f_2930_,
    );
    return v___x_2931_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1(
    mut v_m_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut crate::leanh::LeanObject,
    mut v_inst_2934_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2935_: *mut crate::leanh::LeanObject,
    mut v_m_2936_: *mut crate::leanh::LeanObject,
    mut v_init_2937_: *mut crate::leanh::LeanObject,
    mut v_f_2938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2939_ = crate::leanh::lean_ctor_get(v_inst_2934_, 0);
    v_toBind_2940_ = crate::leanh::lean_ctor_get(v_inst_2934_, 1);
    crate::leanh::lean_inc(v_toBind_2940_);
    v_toPure_2941_ = crate::leanh::lean_ctor_get(v_toApplicative_2939_, 1);
    crate::leanh::lean_inc(v_toPure_2941_);
    v___f_2942_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2942_, 0, v_f_2938_);
    v___x_2943_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(
        v_inst_2934_,
        v___f_2942_,
        v_init_2937_,
        v_m_2936_,
    );
    v___f_2944_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdSetLMVarIdOfMonad___aux__1___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2944_, 0, v_toPure_2941_);
    v___x_2945_ = crate::leanh::lean_apply_4(
        v_toBind_2940_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2943_,
        v___f_2944_,
    );
    return v___x_2945_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___redArg(
    mut v_inst_2946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2947_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2947_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2947_, 2, v_inst_2946_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad(
    mut v_m_2948_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2949_: *mut crate::leanh::LeanObject,
    mut v_inst_2950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2951_ = crate::leanh::lean_alloc_closure(
        l_Lean_instForInLMVarIdMapProdLMVarIdOfMonad___aux__1 as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___x_2951_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2951_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2951_, 2, v_inst_2950_);
    return v___x_2951_;
}
pub unsafe fn l_Lean_instInhabitedLMVarIdMap(
    mut v_00_u03b1_2952_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2953_ = crate::leanh::lean_box(1);
    return v___x_2953_;
}
pub unsafe fn l_Lean_Level_ctorIdx(
    mut v_x_2954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2954_) {
        0 => {
            let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2955_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2955_;
        }
        1 => {
            let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2956_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2956_;
        }
        2 => {
            let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2957_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2957_;
        }
        3 => {
            let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2958_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2958_;
        }
        4 => {
            let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2959_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2959_;
        }
        _ => {
            let mut v___x_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2960_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2960_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorIdx___boxed(
    mut v_x_2961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2962_ = l_Lean_Level_ctorIdx(v_x_2961_);
    crate::leanh::lean_dec(v_x_2961_);
    return v_res_2962_;
}
pub unsafe fn l_Lean_Level_ctorElim___redArg(
    mut v_t_2963_: *mut crate::leanh::LeanObject,
    mut v_k_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2963_) {
        0 => {
            return v_k_2964_;
        }
        2 => {
            let mut v_a_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2965_ = crate::leanh::lean_ctor_get(v_t_2963_, 0);
            crate::leanh::lean_inc(v_a_2965_);
            v_a_2966_ = crate::leanh::lean_ctor_get(v_t_2963_, 1);
            crate::leanh::lean_inc(v_a_2966_);
            crate::leanh::lean_dec_ref_known(v_t_2963_, 2);
            v___x_2967_ = crate::leanh::lean_apply_2(v_k_2964_, v_a_2965_, v_a_2966_);
            return v___x_2967_;
        }
        3 => {
            let mut v_a_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2968_ = crate::leanh::lean_ctor_get(v_t_2963_, 0);
            crate::leanh::lean_inc(v_a_2968_);
            v_a_2969_ = crate::leanh::lean_ctor_get(v_t_2963_, 1);
            crate::leanh::lean_inc(v_a_2969_);
            crate::leanh::lean_dec_ref_known(v_t_2963_, 2);
            v___x_2970_ = crate::leanh::lean_apply_2(v_k_2964_, v_a_2968_, v_a_2969_);
            return v___x_2970_;
        }
        _ => {
            let mut v_a_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_2971_ = crate::leanh::lean_ctor_get(v_t_2963_, 0);
            crate::leanh::lean_inc(v_a_2971_);
            crate::leanh::lean_dec(v_t_2963_);
            v___x_2972_ = crate::leanh::lean_apply_1(v_k_2964_, v_a_2971_);
            return v___x_2972_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorElim(
    mut v_motive_2973_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2974_: *mut crate::leanh::LeanObject,
    mut v_t_2975_: *mut crate::leanh::LeanObject,
    mut v_h_2976_: *mut crate::leanh::LeanObject,
    mut v_k_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2978_ = l_Lean_Level_ctorElim___redArg(v_t_2975_, v_k_2977_);
    return v___x_2978_;
}
pub unsafe fn l_Lean_Level_ctorElim___boxed(
    mut v_motive_2979_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2980_: *mut crate::leanh::LeanObject,
    mut v_t_2981_: *mut crate::leanh::LeanObject,
    mut v_h_2982_: *mut crate::leanh::LeanObject,
    mut v_k_2983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2984_ = l_Lean_Level_ctorElim(
        v_motive_2979_,
        v_ctorIdx_2980_,
        v_t_2981_,
        v_h_2982_,
        v_k_2983_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2980_);
    return v_res_2984_;
}
pub unsafe fn l_Lean_Level_zero_elim___redArg(
    mut v_t_2985_: *mut crate::leanh::LeanObject,
    mut v_zero_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2987_ = l_Lean_Level_ctorElim___redArg(v_t_2985_, v_zero_2986_);
    return v___x_2987_;
}
pub unsafe fn l_Lean_Level_zero_elim(
    mut v_motive_2988_: *mut crate::leanh::LeanObject,
    mut v_t_2989_: *mut crate::leanh::LeanObject,
    mut v_h_2990_: *mut crate::leanh::LeanObject,
    mut v_zero_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = l_Lean_Level_ctorElim___redArg(v_t_2989_, v_zero_2991_);
    return v___x_2992_;
}
pub unsafe fn l_Lean_Level_succ_elim___redArg(
    mut v_t_2993_: *mut crate::leanh::LeanObject,
    mut v_succ_2994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = l_Lean_Level_ctorElim___redArg(v_t_2993_, v_succ_2994_);
    return v___x_2995_;
}
pub unsafe fn l_Lean_Level_succ_elim(
    mut v_motive_2996_: *mut crate::leanh::LeanObject,
    mut v_t_2997_: *mut crate::leanh::LeanObject,
    mut v_h_2998_: *mut crate::leanh::LeanObject,
    mut v_succ_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3000_ = l_Lean_Level_ctorElim___redArg(v_t_2997_, v_succ_2999_);
    return v___x_3000_;
}
pub unsafe fn l_Lean_Level_max_elim___redArg(
    mut v_t_3001_: *mut crate::leanh::LeanObject,
    mut v_max_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3003_ = l_Lean_Level_ctorElim___redArg(v_t_3001_, v_max_3002_);
    return v___x_3003_;
}
pub unsafe fn l_Lean_Level_max_elim(
    mut v_motive_3004_: *mut crate::leanh::LeanObject,
    mut v_t_3005_: *mut crate::leanh::LeanObject,
    mut v_h_3006_: *mut crate::leanh::LeanObject,
    mut v_max_3007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3008_ = l_Lean_Level_ctorElim___redArg(v_t_3005_, v_max_3007_);
    return v___x_3008_;
}
pub unsafe fn l_Lean_Level_imax_elim___redArg(
    mut v_t_3009_: *mut crate::leanh::LeanObject,
    mut v_imax_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Lean_Level_ctorElim___redArg(v_t_3009_, v_imax_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Lean_Level_imax_elim(
    mut v_motive_3012_: *mut crate::leanh::LeanObject,
    mut v_t_3013_: *mut crate::leanh::LeanObject,
    mut v_h_3014_: *mut crate::leanh::LeanObject,
    mut v_imax_3015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_Level_ctorElim___redArg(v_t_3013_, v_imax_3015_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_Level_param_elim___redArg(
    mut v_t_3017_: *mut crate::leanh::LeanObject,
    mut v_param_3018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3019_ = l_Lean_Level_ctorElim___redArg(v_t_3017_, v_param_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_Level_param_elim(
    mut v_motive_3020_: *mut crate::leanh::LeanObject,
    mut v_t_3021_: *mut crate::leanh::LeanObject,
    mut v_h_3022_: *mut crate::leanh::LeanObject,
    mut v_param_3023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3024_ = l_Lean_Level_ctorElim___redArg(v_t_3021_, v_param_3023_);
    return v___x_3024_;
}
pub unsafe fn l_Lean_Level_mvar_elim___redArg(
    mut v_t_3025_: *mut crate::leanh::LeanObject,
    mut v_mvar_3026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_Level_ctorElim___redArg(v_t_3025_, v_mvar_3026_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_Level_mvar_elim(
    mut v_motive_3028_: *mut crate::leanh::LeanObject,
    mut v_t_3029_: *mut crate::leanh::LeanObject,
    mut v_h_3030_: *mut crate::leanh::LeanObject,
    mut v_mvar_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_Level_ctorElim___redArg(v_t_3029_, v_mvar_3031_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Level_casesOn___override___redArg(
    mut v_t_3033_: *mut crate::leanh::LeanObject,
    mut v_zero_3034_: *mut crate::leanh::LeanObject,
    mut v_succ_3035_: *mut crate::leanh::LeanObject,
    mut v_max_3036_: *mut crate::leanh::LeanObject,
    mut v_imax_3037_: *mut crate::leanh::LeanObject,
    mut v_param_3038_: *mut crate::leanh::LeanObject,
    mut v_mvar_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3033_) {
        0 => {
            crate::leanh::lean_dec(v_mvar_3039_);
            crate::leanh::lean_dec(v_param_3038_);
            crate::leanh::lean_dec(v_imax_3037_);
            crate::leanh::lean_dec(v_max_3036_);
            crate::leanh::lean_dec(v_succ_3035_);
            crate::leanh::lean_inc(v_zero_3034_);
            return v_zero_3034_;
        }
        1 => {
            let mut v_a_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3039_);
            crate::leanh::lean_dec(v_param_3038_);
            crate::leanh::lean_dec(v_imax_3037_);
            crate::leanh::lean_dec(v_max_3036_);
            v_a_3040_ = crate::leanh::lean_ctor_get(v_t_3033_, 0);
            crate::leanh::lean_inc(v_a_3040_);
            crate::leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3041_ = crate::leanh::lean_apply_1(v_succ_3035_, v_a_3040_);
            return v___x_3041_;
        }
        2 => {
            let mut v_a_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3039_);
            crate::leanh::lean_dec(v_param_3038_);
            crate::leanh::lean_dec(v_imax_3037_);
            crate::leanh::lean_dec(v_succ_3035_);
            v_a_3042_ = crate::leanh::lean_ctor_get(v_t_3033_, 0);
            crate::leanh::lean_inc(v_a_3042_);
            v_a_3043_ = crate::leanh::lean_ctor_get(v_t_3033_, 1);
            crate::leanh::lean_inc(v_a_3043_);
            crate::leanh::lean_dec_ref_known(v_t_3033_, 2);
            v___x_3044_ = crate::leanh::lean_apply_2(v_max_3036_, v_a_3042_, v_a_3043_);
            return v___x_3044_;
        }
        3 => {
            let mut v_a_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3039_);
            crate::leanh::lean_dec(v_param_3038_);
            crate::leanh::lean_dec(v_max_3036_);
            crate::leanh::lean_dec(v_succ_3035_);
            v_a_3045_ = crate::leanh::lean_ctor_get(v_t_3033_, 0);
            crate::leanh::lean_inc(v_a_3045_);
            v_a_3046_ = crate::leanh::lean_ctor_get(v_t_3033_, 1);
            crate::leanh::lean_inc(v_a_3046_);
            crate::leanh::lean_dec_ref_known(v_t_3033_, 2);
            v___x_3047_ = crate::leanh::lean_apply_2(v_imax_3037_, v_a_3045_, v_a_3046_);
            return v___x_3047_;
        }
        4 => {
            let mut v_a_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3039_);
            crate::leanh::lean_dec(v_imax_3037_);
            crate::leanh::lean_dec(v_max_3036_);
            crate::leanh::lean_dec(v_succ_3035_);
            v_a_3048_ = crate::leanh::lean_ctor_get(v_t_3033_, 0);
            crate::leanh::lean_inc(v_a_3048_);
            crate::leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3049_ = crate::leanh::lean_apply_1(v_param_3038_, v_a_3048_);
            return v___x_3049_;
        }
        _ => {
            let mut v_a_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_param_3038_);
            crate::leanh::lean_dec(v_imax_3037_);
            crate::leanh::lean_dec(v_max_3036_);
            crate::leanh::lean_dec(v_succ_3035_);
            v_a_3050_ = crate::leanh::lean_ctor_get(v_t_3033_, 0);
            crate::leanh::lean_inc(v_a_3050_);
            crate::leanh::lean_dec_ref_known(v_t_3033_, 1);
            v___x_3051_ = crate::leanh::lean_apply_1(v_mvar_3039_, v_a_3050_);
            return v___x_3051_;
        }
    }
}
pub unsafe fn l_Lean_Level_casesOn___override___redArg___boxed(
    mut v_t_3052_: *mut crate::leanh::LeanObject,
    mut v_zero_3053_: *mut crate::leanh::LeanObject,
    mut v_succ_3054_: *mut crate::leanh::LeanObject,
    mut v_max_3055_: *mut crate::leanh::LeanObject,
    mut v_imax_3056_: *mut crate::leanh::LeanObject,
    mut v_param_3057_: *mut crate::leanh::LeanObject,
    mut v_mvar_3058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3059_ = l_Lean_Level_casesOn___override___redArg(
        v_t_3052_,
        v_zero_3053_,
        v_succ_3054_,
        v_max_3055_,
        v_imax_3056_,
        v_param_3057_,
        v_mvar_3058_,
    );
    crate::leanh::lean_dec(v_zero_3053_);
    return v_res_3059_;
}
pub unsafe fn l_Lean_Level_casesOn___override(
    mut v_motive_3060_: *mut crate::leanh::LeanObject,
    mut v_t_3061_: *mut crate::leanh::LeanObject,
    mut v_zero_3062_: *mut crate::leanh::LeanObject,
    mut v_succ_3063_: *mut crate::leanh::LeanObject,
    mut v_max_3064_: *mut crate::leanh::LeanObject,
    mut v_imax_3065_: *mut crate::leanh::LeanObject,
    mut v_param_3066_: *mut crate::leanh::LeanObject,
    mut v_mvar_3067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_3061_) {
        0 => {
            crate::leanh::lean_dec(v_mvar_3067_);
            crate::leanh::lean_dec(v_param_3066_);
            crate::leanh::lean_dec(v_imax_3065_);
            crate::leanh::lean_dec(v_max_3064_);
            crate::leanh::lean_dec(v_succ_3063_);
            crate::leanh::lean_inc(v_zero_3062_);
            return v_zero_3062_;
        }
        1 => {
            let mut v_a_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3067_);
            crate::leanh::lean_dec(v_param_3066_);
            crate::leanh::lean_dec(v_imax_3065_);
            crate::leanh::lean_dec(v_max_3064_);
            v_a_3068_ = crate::leanh::lean_ctor_get(v_t_3061_, 0);
            crate::leanh::lean_inc(v_a_3068_);
            crate::leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3069_ = crate::leanh::lean_apply_1(v_succ_3063_, v_a_3068_);
            return v___x_3069_;
        }
        2 => {
            let mut v_a_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3067_);
            crate::leanh::lean_dec(v_param_3066_);
            crate::leanh::lean_dec(v_imax_3065_);
            crate::leanh::lean_dec(v_succ_3063_);
            v_a_3070_ = crate::leanh::lean_ctor_get(v_t_3061_, 0);
            crate::leanh::lean_inc(v_a_3070_);
            v_a_3071_ = crate::leanh::lean_ctor_get(v_t_3061_, 1);
            crate::leanh::lean_inc(v_a_3071_);
            crate::leanh::lean_dec_ref_known(v_t_3061_, 2);
            v___x_3072_ = crate::leanh::lean_apply_2(v_max_3064_, v_a_3070_, v_a_3071_);
            return v___x_3072_;
        }
        3 => {
            let mut v_a_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3067_);
            crate::leanh::lean_dec(v_param_3066_);
            crate::leanh::lean_dec(v_max_3064_);
            crate::leanh::lean_dec(v_succ_3063_);
            v_a_3073_ = crate::leanh::lean_ctor_get(v_t_3061_, 0);
            crate::leanh::lean_inc(v_a_3073_);
            v_a_3074_ = crate::leanh::lean_ctor_get(v_t_3061_, 1);
            crate::leanh::lean_inc(v_a_3074_);
            crate::leanh::lean_dec_ref_known(v_t_3061_, 2);
            v___x_3075_ = crate::leanh::lean_apply_2(v_imax_3065_, v_a_3073_, v_a_3074_);
            return v___x_3075_;
        }
        4 => {
            let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_mvar_3067_);
            crate::leanh::lean_dec(v_imax_3065_);
            crate::leanh::lean_dec(v_max_3064_);
            crate::leanh::lean_dec(v_succ_3063_);
            v_a_3076_ = crate::leanh::lean_ctor_get(v_t_3061_, 0);
            crate::leanh::lean_inc(v_a_3076_);
            crate::leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3077_ = crate::leanh::lean_apply_1(v_param_3066_, v_a_3076_);
            return v___x_3077_;
        }
        _ => {
            let mut v_a_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_param_3066_);
            crate::leanh::lean_dec(v_imax_3065_);
            crate::leanh::lean_dec(v_max_3064_);
            crate::leanh::lean_dec(v_succ_3063_);
            v_a_3078_ = crate::leanh::lean_ctor_get(v_t_3061_, 0);
            crate::leanh::lean_inc(v_a_3078_);
            crate::leanh::lean_dec_ref_known(v_t_3061_, 1);
            v___x_3079_ = crate::leanh::lean_apply_1(v_mvar_3067_, v_a_3078_);
            return v___x_3079_;
        }
    }
}
pub unsafe fn l_Lean_Level_casesOn___override___boxed(
    mut v_motive_3080_: *mut crate::leanh::LeanObject,
    mut v_t_3081_: *mut crate::leanh::LeanObject,
    mut v_zero_3082_: *mut crate::leanh::LeanObject,
    mut v_succ_3083_: *mut crate::leanh::LeanObject,
    mut v_max_3084_: *mut crate::leanh::LeanObject,
    mut v_imax_3085_: *mut crate::leanh::LeanObject,
    mut v_param_3086_: *mut crate::leanh::LeanObject,
    mut v_mvar_3087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_zero_3082_);
    return v_res_3088_;
}
pub unsafe fn _init_l_Lean_Level_zero___override() -> *mut crate::leanh::LeanObject {
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3089_ = crate::leanh::lean_box(0);
    return v___x_3089_;
}
pub unsafe fn _init_l_Lean_Level_data___override___closed__0() -> u64 {
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3092_: u64 = 0;
    let mut v___x_3093_: u64 = 0;
    v___x_3090_ = 0;
    v___x_3091_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3092_ = 2221u64;
    v___x_3093_ = lean_level_mk_data(v___x_3092_, v___x_3091_, v___x_3090_, v___x_3090_);
    return v___x_3093_;
}
pub unsafe fn l_Lean_Level_data___override(mut v_x_3094_: *mut crate::leanh::LeanObject) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_3094_) {
        0 => {
            let mut v___x_3095_: u64 = 0;
            v___x_3095_ = crate::leanh::lean_uint64_once(
                core::ptr::addr_of_mut!(l_Lean_Level_data___override___closed__0),
                core::ptr::addr_of_mut!(l_Lean_Level_data___override___closed__0_once),
                _init_l_Lean_Level_data___override___closed__0,
            );
            return v___x_3095_;
        }
        2 => {
            let mut v_data_3096_: u64 = 0;
            v_data_3096_ = crate::leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            return v_data_3096_;
        }
        3 => {
            let mut v_data_3097_: u64 = 0;
            v_data_3097_ = crate::leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
            );
            return v_data_3097_;
        }
        _ => {
            let mut v_data_3098_: u64 = 0;
            v_data_3098_ = crate::leanh::lean_ctor_get_uint64(
                v_x_3094_,
                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            );
            return v_data_3098_;
        }
    }
}
pub unsafe fn l_Lean_Level_data___override___boxed(
    mut v_x_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: u64 = 0;
    let mut v_r_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_Lean_Level_data___override(v_x_3099_);
    crate::leanh::lean_dec(v_x_3099_);
    v_r_3101_ = crate::leanh::lean_box_uint64(v_res_3100_);
    return v_r_3101_;
}
pub unsafe fn l_Lean_Level_succ___override(
    mut v_a_3102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3103_: u64 = 0;
    let mut v___x_3104_: u64 = 0;
    let mut v___x_3105_: u64 = 0;
    let mut v___x_3106_: u64 = 0;
    let mut v___x_3107_: u32 = 0;
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: u64 = 0;
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3103_ = 2243u64;
    v___x_3104_ = l_Lean_Level_data___override(v_a_3102_);
    v___x_3105_ = l_Lean_Level_Data_hash(v___x_3104_);
    v___x_3106_ = lean_uint64_mix_hash(v___x_3103_, v___x_3105_);
    v___x_3107_ = l_Lean_Level_Data_depth(v___x_3104_);
    v___x_3108_ = lean_uint32_to_nat(v___x_3107_);
    v___x_3109_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3110_ = lean_nat_add(v___x_3108_, v___x_3109_);
    crate::leanh::lean_dec(v___x_3108_);
    v___x_3111_ = l_Lean_Level_Data_hasMVar(v___x_3104_);
    v___x_3112_ = l_Lean_Level_Data_hasParam(v___x_3104_);
    v___x_3113_ = lean_level_mk_data(v___x_3106_, v___x_3110_, v___x_3111_, v___x_3112_);
    v___x_3114_ = crate::leanh::lean_alloc_ctor(1, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3114_, 0, v_a_3102_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3114_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3113_,
    );
    return v___x_3114_;
}
pub unsafe fn l_Lean_Level_max___override(
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_a_3116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3117_: u64 = 0;
    let mut v___x_3118_: u64 = 0;
    let mut v___x_3119_: u64 = 0;
    let mut v___x_3120_: u64 = 0;
    let mut v___x_3121_: u64 = 0;
    let mut v___x_3122_: u64 = 0;
    let mut v___x_3123_: u64 = 0;
    let mut v___y_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3126_: u8 = 0;
    let mut v___y_3127_: u8 = 0;
    let mut v___x_3128_: u64 = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3132_: u8 = 0;
    let mut v___x_3133_: u8 = 0;
    let mut v___x_3134_: u8 = 0;
    let mut v___y_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: u8 = 0;
    let mut v___x_3141_: u32 = 0;
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u32 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v___x_3144_);
                    v___y_3136_ = v___x_3142_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3142_);
                    v___y_3136_ = v___x_3144_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3128_ =
                    lean_level_mk_data(v___x_3123_, v___y_3125_, v___y_3126_, v___y_3127_);
                v___x_3129_ = crate::leanh::lean_alloc_ctor(2, 2, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3129_, 0, v_a_3115_);
                crate::leanh::lean_ctor_set(v___x_3129_, 1, v_a_3116_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3129_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
                v___x_3137_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3138_ = lean_nat_add(v___y_3136_, v___x_3137_);
                crate::leanh::lean_dec(v___y_3136_);
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
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3148_: u64 = 0;
    let mut v___x_3149_: u64 = 0;
    let mut v___x_3150_: u64 = 0;
    let mut v___x_3151_: u64 = 0;
    let mut v___x_3152_: u64 = 0;
    let mut v___x_3153_: u64 = 0;
    let mut v___x_3154_: u64 = 0;
    let mut v___y_3156_: u8 = 0;
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: u8 = 0;
    let mut v___x_3159_: u64 = 0;
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: u8 = 0;
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: u8 = 0;
    let mut v___y_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: u8 = 0;
    let mut v___x_3171_: u8 = 0;
    let mut v___x_3172_: u32 = 0;
    let mut v___x_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: u32 = 0;
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v___x_3175_);
                    v___y_3167_ = v___x_3173_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3173_);
                    v___y_3167_ = v___x_3175_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3159_ =
                    lean_level_mk_data(v___x_3154_, v___y_3157_, v___y_3156_, v___y_3158_);
                v___x_3160_ = crate::leanh::lean_alloc_ctor(3, 2, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3160_, 0, v_a_3146_);
                crate::leanh::lean_ctor_set(v___x_3160_, 1, v_a_3147_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3160_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
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
                v___x_3168_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3169_ = lean_nat_add(v___y_3167_, v___x_3168_);
                crate::leanh::lean_dec(v___y_3167_);
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
    mut v_a_3177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3178_: u64 = 0;
    let mut v___y_3180_: u64 = 0;
    let mut v___x_3181_: u64 = 0;
    let mut v___x_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: u8 = 0;
    let mut v___x_3185_: u64 = 0;
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u64 = 0;
    let mut v_hash_3188_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3178_ = 2239u64;
                if crate::leanh::lean_obj_tag(v_a_3177_) == 0 {
                    v___x_3187_ = crate::leanh::lean_uint64_once(
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
                    v_hash_3188_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_3177_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3180_ = v_hash_3188_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3181_ = lean_uint64_mix_hash(v___x_3178_, v___y_3180_);
                v___x_3182_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3183_ = 0;
                v___x_3184_ = 1;
                v___x_3185_ =
                    lean_level_mk_data(v___x_3181_, v___x_3182_, v___x_3183_, v___x_3184_);
                v___x_3186_ = crate::leanh::lean_alloc_ctor(4, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3186_, 0, v_a_3177_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3186_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3185_,
                );
                return v___x_3186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_mvar___override(
    mut v_a_3189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3190_: u64 = 0;
    let mut v___x_3191_: u64 = 0;
    let mut v___x_3192_: u64 = 0;
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: u8 = 0;
    let mut v___x_3196_: u64 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3190_ = 2237u64;
    v___x_3191_ = l_Lean_instHashableLevelMVarId_hash(v_a_3189_);
    v___x_3192_ = lean_uint64_mix_hash(v___x_3190_, v___x_3191_);
    v___x_3193_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3194_ = 1;
    v___x_3195_ = 0;
    v___x_3196_ = lean_level_mk_data(v___x_3192_, v___x_3193_, v___x_3194_, v___x_3195_);
    v___x_3197_ = crate::leanh::lean_alloc_ctor(5, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_3197_, 0, v_a_3189_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_3197_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_3196_,
    );
    return v___x_3197_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevel_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3198_ = crate::leanh::lean_box(0);
    return v___x_3198_;
}
pub unsafe fn _init_l_Lean_instInhabitedLevel() -> *mut crate::leanh::LeanObject {
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3199_ = crate::leanh::lean_box(0);
    return v___x_3199_;
}
pub unsafe fn _init_l_Lean_instReprLevel_repr___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3203_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3204_ = lean_nat_to_int(v___x_3203_);
    return v___x_3204_;
}
pub unsafe fn _init_l_Lean_instReprLevel_repr___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3205_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_3206_ = lean_nat_to_int(v___x_3205_);
    return v___x_3206_;
}
pub unsafe fn l_Lean_instReprLevel_repr(
    mut v_x_3237_: *mut crate::leanh::LeanObject,
    mut v_prec_3238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: u8 = 0;
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: u8 = 0;
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: u8 = 0;
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: u8 = 0;
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: u8 = 0;
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: u8 = 0;
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: u8 = 0;
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: u8 = 0;
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: u8 = 0;
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3237_) {
                0 => {
                    v___x_3246_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3247_ = lean_nat_dec_le(v___x_3246_, v_prec_3238_);
                    if v___x_3247_ == 0 {
                        v___x_3248_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3240_ = v___x_3248_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3249_ = crate::leanh::lean_obj_once(
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
                    v_a_3250_ = crate::leanh::lean_ctor_get(v_x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3250_);
                    crate::leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3251_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3261_ = lean_nat_dec_le(v___x_3251_, v_prec_3238_);
                    if v___x_3261_ == 0 {
                        v___x_3262_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3253_ = v___x_3262_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3263_ = crate::leanh::lean_obj_once(
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
                    v_a_3264_ = crate::leanh::lean_ctor_get(v_x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3264_);
                    v_a_3265_ = crate::leanh::lean_ctor_get(v_x_3237_, 1);
                    crate::leanh::lean_inc(v_a_3265_);
                    crate::leanh::lean_dec_ref_known(v_x_3237_, 2);
                    v___x_3266_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3280_ = lean_nat_dec_le(v___x_3266_, v_prec_3238_);
                    if v___x_3280_ == 0 {
                        v___x_3281_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3268_ = v___x_3281_;
                        state = 3;
                        continue;
                    } else {
                        v___x_3282_ = crate::leanh::lean_obj_once(
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
                    v_a_3283_ = crate::leanh::lean_ctor_get(v_x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3283_);
                    v_a_3284_ = crate::leanh::lean_ctor_get(v_x_3237_, 1);
                    crate::leanh::lean_inc(v_a_3284_);
                    crate::leanh::lean_dec_ref_known(v_x_3237_, 2);
                    v___x_3285_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3299_ = lean_nat_dec_le(v___x_3285_, v_prec_3238_);
                    if v___x_3299_ == 0 {
                        v___x_3300_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3287_ = v___x_3300_;
                        state = 4;
                        continue;
                    } else {
                        v___x_3301_ = crate::leanh::lean_obj_once(
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
                    v_a_3302_ = crate::leanh::lean_ctor_get(v_x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3302_);
                    crate::leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3313_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3314_ = lean_nat_dec_le(v___x_3313_, v_prec_3238_);
                    if v___x_3314_ == 0 {
                        v___x_3315_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3304_ = v___x_3315_;
                        state = 5;
                        continue;
                    } else {
                        v___x_3316_ = crate::leanh::lean_obj_once(
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
                    v_a_3317_ = crate::leanh::lean_ctor_get(v_x_3237_, 0);
                    crate::leanh::lean_inc(v_a_3317_);
                    crate::leanh::lean_dec_ref_known(v_x_3237_, 1);
                    v___x_3328_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_3329_ = lean_nat_dec_le(v___x_3328_, v_prec_3238_);
                    if v___x_3329_ == 0 {
                        v___x_3330_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2),
                            core::ptr::addr_of_mut!(l_Lean_instReprLevel_repr___closed__2_once),
                            _init_l_Lean_instReprLevel_repr___closed__2,
                        );
                        v___y_3319_ = v___x_3330_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3331_ = crate::leanh::lean_obj_once(
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
                crate::leanh::lean_inc(v___y_3240_);
                v___x_3242_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3242_, 0, v___y_3240_);
                crate::leanh::lean_ctor_set(v___x_3242_, 1, v___x_3241_);
                v___x_3243_ = 0;
                v___x_3244_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3244_, 0, v___x_3242_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3244_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3243_,
                );
                v___x_3245_ = l_Repr_addAppParen(v___x_3244_, v_prec_3238_);
                return v___x_3245_;
            }
            2 => {
                v___x_3254_ = l_Lean_instReprLevel_repr___closed__6;
                v___x_3255_ = l_Lean_instReprLevel_repr(v_a_3250_, v___x_3251_);
                v___x_3256_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3256_, 0, v___x_3254_);
                crate::leanh::lean_ctor_set(v___x_3256_, 1, v___x_3255_);
                crate::leanh::lean_inc(v___y_3253_);
                v___x_3257_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3257_, 0, v___y_3253_);
                crate::leanh::lean_ctor_set(v___x_3257_, 1, v___x_3256_);
                v___x_3258_ = 0;
                v___x_3259_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3257_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3259_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3258_,
                );
                v___x_3260_ = l_Repr_addAppParen(v___x_3259_, v_prec_3238_);
                return v___x_3260_;
            }
            3 => {
                v___x_3269_ = crate::leanh::lean_box(1);
                v___x_3270_ = l_Lean_instReprLevel_repr___closed__9;
                v___x_3271_ = l_Lean_instReprLevel_repr(v_a_3264_, v___x_3266_);
                v___x_3272_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3272_, 0, v___x_3270_);
                crate::leanh::lean_ctor_set(v___x_3272_, 1, v___x_3271_);
                v___x_3273_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3273_, 0, v___x_3272_);
                crate::leanh::lean_ctor_set(v___x_3273_, 1, v___x_3269_);
                v___x_3274_ = l_Lean_instReprLevel_repr(v_a_3265_, v___x_3266_);
                v___x_3275_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3273_);
                crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3274_);
                crate::leanh::lean_inc(v___y_3268_);
                v___x_3276_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3276_, 0, v___y_3268_);
                crate::leanh::lean_ctor_set(v___x_3276_, 1, v___x_3275_);
                v___x_3277_ = 0;
                v___x_3278_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3278_, 0, v___x_3276_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3278_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3277_,
                );
                v___x_3279_ = l_Repr_addAppParen(v___x_3278_, v_prec_3238_);
                return v___x_3279_;
            }
            4 => {
                v___x_3288_ = crate::leanh::lean_box(1);
                v___x_3289_ = l_Lean_instReprLevel_repr___closed__12;
                v___x_3290_ = l_Lean_instReprLevel_repr(v_a_3283_, v___x_3285_);
                v___x_3291_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3291_, 0, v___x_3289_);
                crate::leanh::lean_ctor_set(v___x_3291_, 1, v___x_3290_);
                v___x_3292_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3291_);
                crate::leanh::lean_ctor_set(v___x_3292_, 1, v___x_3288_);
                v___x_3293_ = l_Lean_instReprLevel_repr(v_a_3284_, v___x_3285_);
                v___x_3294_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3294_, 0, v___x_3292_);
                crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                crate::leanh::lean_inc(v___y_3287_);
                v___x_3295_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3295_, 0, v___y_3287_);
                crate::leanh::lean_ctor_set(v___x_3295_, 1, v___x_3294_);
                v___x_3296_ = 0;
                v___x_3297_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3297_, 0, v___x_3295_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3297_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3296_,
                );
                v___x_3298_ = l_Repr_addAppParen(v___x_3297_, v_prec_3238_);
                return v___x_3298_;
            }
            5 => {
                v___x_3305_ = l_Lean_instReprLevel_repr___closed__15;
                v___x_3306_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3307_ = l_Lean_Name_reprPrec(v_a_3302_, v___x_3306_);
                v___x_3308_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3308_, 0, v___x_3305_);
                crate::leanh::lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                crate::leanh::lean_inc(v___y_3304_);
                v___x_3309_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3309_, 0, v___y_3304_);
                crate::leanh::lean_ctor_set(v___x_3309_, 1, v___x_3308_);
                v___x_3310_ = 0;
                v___x_3311_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3311_, 0, v___x_3309_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3311_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_3310_,
                );
                v___x_3312_ = l_Repr_addAppParen(v___x_3311_, v_prec_3238_);
                return v___x_3312_;
            }
            6 => {
                v___x_3320_ = l_Lean_instReprLevel_repr___closed__18;
                v___x_3321_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_3322_ = l_Lean_Name_reprPrec(v_a_3317_, v___x_3321_);
                v___x_3323_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3323_, 0, v___x_3320_);
                crate::leanh::lean_ctor_set(v___x_3323_, 1, v___x_3322_);
                crate::leanh::lean_inc(v___y_3319_);
                v___x_3324_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3324_, 0, v___y_3319_);
                crate::leanh::lean_ctor_set(v___x_3324_, 1, v___x_3323_);
                v___x_3325_ = 0;
                v___x_3326_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3326_, 0, v___x_3324_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3326_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
    mut v_x_3332_: *mut crate::leanh::LeanObject,
    mut v_prec_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3334_ = l_Lean_instReprLevel_repr(v_x_3332_, v_prec_3333_);
    crate::leanh::lean_dec(v_prec_3333_);
    return v_res_3334_;
}
pub unsafe fn l_Lean_Level_hash(mut v_u_3337_: *mut crate::leanh::LeanObject) -> u64 {
    let mut v___x_3338_: u64 = 0;
    let mut v___x_3339_: u64 = 0;
    v___x_3338_ = l_Lean_Level_data___override(v_u_3337_);
    v___x_3339_ = l_Lean_Level_Data_hash(v___x_3338_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_Level_hash___boxed(
    mut v_u_3340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3341_: u64 = 0;
    let mut v_r_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3341_ = l_Lean_Level_hash(v_u_3340_);
    crate::leanh::lean_dec(v_u_3340_);
    v_r_3342_ = crate::leanh::lean_box_uint64(v_res_3341_);
    return v_r_3342_;
}
pub unsafe fn l_Lean_Level_depth(
    mut v_u_3345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3346_: u64 = 0;
    let mut v___x_3347_: u32 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Lean_Level_data___override(v_u_3345_);
    v___x_3347_ = l_Lean_Level_Data_depth(v___x_3346_);
    v___x_3348_ = lean_uint32_to_nat(v___x_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Lean_Level_depth___boxed(
    mut v_u_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ = l_Lean_Level_depth(v_u_3349_);
    crate::leanh::lean_dec(v_u_3349_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_Level_hasMVar(mut v_u_3351_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3352_: u64 = 0;
    let mut v___x_3353_: u8 = 0;
    v___x_3352_ = l_Lean_Level_data___override(v_u_3351_);
    v___x_3353_ = l_Lean_Level_Data_hasMVar(v___x_3352_);
    return v___x_3353_;
}
pub unsafe fn l_Lean_Level_hasMVar___boxed(
    mut v_u_3354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3355_: u8 = 0;
    let mut v_r_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3355_ = l_Lean_Level_hasMVar(v_u_3354_);
    crate::leanh::lean_dec(v_u_3354_);
    v_r_3356_ = crate::leanh::lean_box((v_res_3355_) as usize);
    return v_r_3356_;
}
pub unsafe fn l_Lean_Level_hasParam(mut v_u_3357_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3358_: u64 = 0;
    let mut v___x_3359_: u8 = 0;
    v___x_3358_ = l_Lean_Level_data___override(v_u_3357_);
    v___x_3359_ = l_Lean_Level_Data_hasParam(v___x_3358_);
    return v___x_3359_;
}
pub unsafe fn l_Lean_Level_hasParam___boxed(
    mut v_u_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3361_: u8 = 0;
    let mut v_r_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3361_ = l_Lean_Level_hasParam(v_u_3360_);
    crate::leanh::lean_dec(v_u_3360_);
    v_r_3362_ = crate::leanh::lean_box((v_res_3361_) as usize);
    return v_r_3362_;
}
pub unsafe fn lean_level_hash(mut v_u_3363_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_3364_: u64 = 0;
    let mut v___x_3365_: u32 = 0;
    v___x_3364_ = l_Lean_Level_hash(v_u_3363_);
    crate::leanh::lean_dec(v_u_3363_);
    v___x_3365_ = lean_uint64_to_uint32(v___x_3364_);
    return v___x_3365_;
}
pub unsafe fn l_Lean_Level_hashEx___boxed(
    mut v_u_3366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3367_: u32 = 0;
    let mut v_r_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3367_ = lean_level_hash(v_u_3366_);
    v_r_3368_ = crate::leanh::lean_box_uint32(v_res_3367_);
    return v_r_3368_;
}
pub unsafe fn lean_level_has_mvar(mut v_u_3369_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3370_: u8 = 0;
    v___x_3370_ = l_Lean_Level_hasMVar(v_u_3369_);
    crate::leanh::lean_dec(v_u_3369_);
    return v___x_3370_;
}
pub unsafe fn l_Lean_Level_hasMVarEx___boxed(
    mut v_u_3371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3372_: u8 = 0;
    let mut v_r_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3372_ = lean_level_has_mvar(v_u_3371_);
    v_r_3373_ = crate::leanh::lean_box((v_res_3372_) as usize);
    return v_r_3373_;
}
pub unsafe fn lean_level_has_param(mut v_u_3374_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3375_: u8 = 0;
    v___x_3375_ = l_Lean_Level_hasParam(v_u_3374_);
    crate::leanh::lean_dec(v_u_3374_);
    return v___x_3375_;
}
pub unsafe fn l_Lean_Level_hasParamEx___boxed(
    mut v_u_3376_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3377_: u8 = 0;
    let mut v_r_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3377_ = lean_level_has_param(v_u_3376_);
    v_r_3378_ = crate::leanh::lean_box((v_res_3377_) as usize);
    return v_r_3378_;
}
pub unsafe fn lean_level_depth(mut v_u_3379_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_3380_: u64 = 0;
    let mut v___x_3381_: u32 = 0;
    v___x_3380_ = l_Lean_Level_data___override(v_u_3379_);
    crate::leanh::lean_dec(v_u_3379_);
    v___x_3381_ = l_Lean_Level_Data_depth(v___x_3380_);
    return v___x_3381_;
}
pub unsafe fn l_Lean_Level_depthEx___boxed(
    mut v_u_3382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3383_: u32 = 0;
    let mut v_r_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3383_ = lean_level_depth(v_u_3382_);
    v_r_3384_ = crate::leanh::lean_box_uint32(v_res_3383_);
    return v_r_3384_;
}
pub unsafe fn _init_l_Lean_levelZero() -> *mut crate::leanh::LeanObject {
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3385_ = crate::leanh::lean_box(0);
    return v___x_3385_;
}
pub unsafe fn l_Lean_mkLevelMVar(
    mut v_mvarId_3386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3387_ = l_Lean_Level_mvar___override(v_mvarId_3386_);
    return v___x_3387_;
}
pub unsafe fn l_Lean_mkLevelParam(
    mut v_name_3388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3389_ = l_Lean_Level_param___override(v_name_3388_);
    return v___x_3389_;
}
pub unsafe fn l_Lean_mkLevelSucc(
    mut v_u_3390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3391_ = l_Lean_Level_succ___override(v_u_3390_);
    return v___x_3391_;
}
pub unsafe fn l_Lean_mkLevelMax(
    mut v_u_3392_: *mut crate::leanh::LeanObject,
    mut v_v_3393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3394_ = l_Lean_Level_max___override(v_u_3392_, v_v_3393_);
    return v___x_3394_;
}
pub unsafe fn l_Lean_mkLevelIMax(
    mut v_u_3395_: *mut crate::leanh::LeanObject,
    mut v_v_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3397_ = l_Lean_Level_imax___override(v_u_3395_, v_v_3396_);
    return v___x_3397_;
}
pub unsafe fn _init_l_Lean_Level_one___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3398_ = crate::leanh::lean_box(0);
    v___x_3399_ = l_Lean_Level_succ___override(v___x_3398_);
    return v___x_3399_;
}
pub unsafe fn _init_l_Lean_Level_one() -> *mut crate::leanh::LeanObject {
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3400_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0_once),
        _init_l_Lean_Level_one___closed__0,
    );
    return v___x_3400_;
}
pub unsafe fn _init_l_Lean_levelOne() -> *mut crate::leanh::LeanObject {
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3401_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_one___closed__0_once),
        _init_l_Lean_Level_one___closed__0,
    );
    return v___x_3401_;
}
pub unsafe fn lean_level_mk_zero(
    mut v_x_3402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = crate::leanh::lean_box(0);
    return v___x_3403_;
}
pub unsafe fn lean_level_mk_succ(
    mut v_u_3404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3405_ = l_Lean_Level_succ___override(v_u_3404_);
    return v___x_3405_;
}
pub unsafe fn lean_level_mk_mvar(
    mut v_mvarId_3406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3407_ = l_Lean_Level_mvar___override(v_mvarId_3406_);
    return v___x_3407_;
}
pub unsafe fn lean_level_mk_param(
    mut v_name_3408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3409_ = l_Lean_Level_param___override(v_name_3408_);
    return v___x_3409_;
}
pub unsafe fn lean_level_mk_max(
    mut v_u_3410_: *mut crate::leanh::LeanObject,
    mut v_v_3411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3412_ = l_Lean_Level_max___override(v_u_3410_, v_v_3411_);
    return v___x_3412_;
}
pub unsafe fn lean_level_mk_imax(
    mut v_u_3413_: *mut crate::leanh::LeanObject,
    mut v_v_3414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_Level_imax___override(v_u_3413_, v_v_3414_);
    return v___x_3415_;
}
pub unsafe fn l_Lean_Level_isZero(mut v_x_3416_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3416_) == 0 {
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
    mut v_x_3419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3420_: u8 = 0;
    let mut v_r_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3420_ = l_Lean_Level_isZero(v_x_3419_);
    crate::leanh::lean_dec(v_x_3419_);
    v_r_3421_ = crate::leanh::lean_box((v_res_3420_) as usize);
    return v_r_3421_;
}
pub unsafe fn l_Lean_Level_isSucc(mut v_x_3422_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3422_) == 1 {
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
    mut v_x_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3426_: u8 = 0;
    let mut v_r_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3426_ = l_Lean_Level_isSucc(v_x_3425_);
    crate::leanh::lean_dec(v_x_3425_);
    v_r_3427_ = crate::leanh::lean_box((v_res_3426_) as usize);
    return v_r_3427_;
}
pub unsafe fn l_Lean_Level_isMax(mut v_x_3428_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3428_) == 2 {
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
    mut v_x_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3432_: u8 = 0;
    let mut v_r_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3432_ = l_Lean_Level_isMax(v_x_3431_);
    crate::leanh::lean_dec(v_x_3431_);
    v_r_3433_ = crate::leanh::lean_box((v_res_3432_) as usize);
    return v_r_3433_;
}
pub unsafe fn l_Lean_Level_isIMax(mut v_x_3434_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3434_) == 3 {
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
    mut v_x_3437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3438_: u8 = 0;
    let mut v_r_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3438_ = l_Lean_Level_isIMax(v_x_3437_);
    crate::leanh::lean_dec(v_x_3437_);
    v_r_3439_ = crate::leanh::lean_box((v_res_3438_) as usize);
    return v_r_3439_;
}
pub unsafe fn l_Lean_Level_isMaxIMax(mut v_x_3440_: *mut crate::leanh::LeanObject) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_3440_) {
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
    mut v_x_3444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3445_: u8 = 0;
    let mut v_r_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Lean_Level_isMaxIMax(v_x_3444_);
    crate::leanh::lean_dec(v_x_3444_);
    v_r_3446_ = crate::leanh::lean_box((v_res_3445_) as usize);
    return v_r_3446_;
}
pub unsafe fn l_Lean_Level_isParam(mut v_x_3447_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3447_) == 4 {
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
    mut v_x_3450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3451_: u8 = 0;
    let mut v_r_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3451_ = l_Lean_Level_isParam(v_x_3450_);
    crate::leanh::lean_dec(v_x_3450_);
    v_r_3452_ = crate::leanh::lean_box((v_res_3451_) as usize);
    return v_r_3452_;
}
pub unsafe fn l_Lean_Level_isMVar(mut v_x_3453_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3453_) == 5 {
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
    mut v_x_3456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3457_: u8 = 0;
    let mut v_r_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3457_ = l_Lean_Level_isMVar(v_x_3456_);
    crate::leanh::lean_dec(v_x_3456_);
    v_r_3458_ = crate::leanh::lean_box((v_res_3457_) as usize);
    return v_r_3458_;
}
pub unsafe fn l_panic___at___00Lean_Level_mvarId_x21_spec__0(
    mut v_msg_3459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3460_ = crate::leanh::lean_box(0);
    v___x_3461_ = lean_panic_fn_borrowed(v___x_3460_, v_msg_3459_);
    return v___x_3461_;
}
pub unsafe fn _init_l_Lean_Level_mvarId_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l_Lean_Level_mvarId_x21___closed__2;
    v___x_3466_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_3467_ = crate::leanh::lean_unsigned_to_nat(195);
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
    mut v_x_3471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3471_) == 5 {
        let mut v_a_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3472_ = crate::leanh::lean_ctor_get(v_x_3471_, 0);
        crate::leanh::lean_inc(v_a_3472_);
        return v_a_3472_;
    } else {
        let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3473_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Level_mvarId_x21___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Level_mvarId_x21___closed__3_once),
            _init_l_Lean_Level_mvarId_x21___closed__3,
        );
        v___x_3474_ = l_panic___at___00Lean_Level_mvarId_x21_spec__0(v___x_3473_);
        return v___x_3474_;
    }
}
pub unsafe fn l_Lean_Level_mvarId_x21___boxed(
    mut v_x_3475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l_Lean_Level_mvarId_x21(v_x_3475_);
    crate::leanh::lean_dec(v_x_3475_);
    return v_res_3476_;
}
pub unsafe fn l_Lean_Level_isNeverZero(mut v_x_3477_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: u8 = 0;
    let mut v_a_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: u8 = 0;
    let mut v_a_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3477_) {
                0 => {
                    v___x_3478_ = 0;
                    return v___x_3478_;
                }
                1 => {
                    v___x_3479_ = 1;
                    return v___x_3479_;
                }
                2 => {
                    v_a_3480_ = crate::leanh::lean_ctor_get(v_x_3477_, 0);
                    v_a_3481_ = crate::leanh::lean_ctor_get(v_x_3477_, 1);
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
                    v_a_3484_ = crate::leanh::lean_ctor_get(v_x_3477_, 1);
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
    mut v_x_3487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3488_: u8 = 0;
    let mut v_r_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3488_ = l_Lean_Level_isNeverZero(v_x_3487_);
    crate::leanh::lean_dec(v_x_3487_);
    v_r_3489_ = crate::leanh::lean_box((v_res_3488_) as usize);
    return v_r_3489_;
}
pub unsafe fn l_Lean_Level_isAlwaysZero(mut v_x_3490_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3491_: u8 = 0;
    let mut v_a_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: u8 = 0;
    let mut v_a_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3490_) {
                0 => {
                    v___x_3491_ = 1;
                    return v___x_3491_;
                }
                2 => {
                    v_a_3492_ = crate::leanh::lean_ctor_get(v_x_3490_, 0);
                    v_a_3493_ = crate::leanh::lean_ctor_get(v_x_3490_, 1);
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
                    v_a_3496_ = crate::leanh::lean_ctor_get(v_x_3490_, 1);
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
    mut v_x_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3500_: u8 = 0;
    let mut v_r_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3500_ = l_Lean_Level_isAlwaysZero(v_x_3499_);
    crate::leanh::lean_dec(v_x_3499_);
    v_r_3501_ = crate::leanh::lean_box((v_res_3500_) as usize);
    return v_r_3501_;
}
pub unsafe fn l_Lean_Level_ofNat(
    mut v_x_3502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3504_: u8 = 0;
    v_zero_3503_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_3504_ = lean_nat_dec_eq(v_x_3502_, v_zero_3503_);
    if v_isZero_3504_ == 1 {
        let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3505_ = crate::leanh::lean_box(0);
        return v___x_3505_;
    } else {
        let mut v_one_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_3506_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_3507_ = lean_nat_sub(v_x_3502_, v_one_3506_);
        v___x_3508_ = l_Lean_Level_ofNat(v_n_3507_);
        crate::leanh::lean_dec(v_n_3507_);
        v___x_3509_ = l_Lean_Level_succ___override(v___x_3508_);
        return v___x_3509_;
    }
}
pub unsafe fn l_Lean_Level_ofNat___boxed(
    mut v_x_3510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3511_ = l_Lean_Level_ofNat(v_x_3510_);
    crate::leanh::lean_dec(v_x_3510_);
    return v_res_3511_;
}
pub unsafe fn l_Lean_Level_instOfNat(
    mut v_n_3512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3513_ = l_Lean_Level_ofNat(v_n_3512_);
    return v___x_3513_;
}
pub unsafe fn l_Lean_Level_instOfNat___boxed(
    mut v_n_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3515_ = l_Lean_Level_instOfNat(v_n_3514_);
    crate::leanh::lean_dec(v_n_3514_);
    return v_res_3515_;
}
pub unsafe fn l_Lean_Level_addOffsetAux(
    mut v_x_3516_: *mut crate::leanh::LeanObject,
    mut v_x_3517_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_3519_: u8 = 0;
    let mut v_one_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3518_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_3519_ = lean_nat_dec_eq(v_x_3516_, v_zero_3518_);
                if v_isZero_3519_ == 1 {
                    crate::leanh::lean_dec(v_x_3516_);
                    return v_x_3517_;
                } else {
                    v_one_3520_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_3521_ = lean_nat_sub(v_x_3516_, v_one_3520_);
                    crate::leanh::lean_dec(v_x_3516_);
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
    mut v_u_3524_: *mut crate::leanh::LeanObject,
    mut v_n_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Level_addOffsetAux(v_n_3525_, v_u_3524_);
    return v___x_3526_;
}
pub unsafe fn l_Lean_Level_isExplicit(mut v_x_3527_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_3528_: u8 = 0;
    let mut v_a_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: u8 = 0;
    let mut v___x_3531_: u8 = 0;
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3527_) {
                0 => {
                    v___x_3528_ = 1;
                    return v___x_3528_;
                }
                1 => {
                    v_a_3529_ = crate::leanh::lean_ctor_get(v_x_3527_, 0);
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
    mut v_x_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3536_: u8 = 0;
    let mut v_r_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3536_ = l_Lean_Level_isExplicit(v_x_3535_);
    crate::leanh::lean_dec(v_x_3535_);
    v_r_3537_ = crate::leanh::lean_box((v_res_3536_) as usize);
    return v_r_3537_;
}
pub unsafe fn l_Lean_Level_getOffsetAux(
    mut v_x_3538_: *mut crate::leanh::LeanObject,
    mut v_x_3539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3538_) == 1 {
                    v_a_3540_ = crate::leanh::lean_ctor_get(v_x_3538_, 0);
                    v___x_3541_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3542_ = lean_nat_add(v_x_3539_, v___x_3541_);
                    crate::leanh::lean_dec(v_x_3539_);
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
    mut v_x_3544_: *mut crate::leanh::LeanObject,
    mut v_x_3545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3546_ = l_Lean_Level_getOffsetAux(v_x_3544_, v_x_3545_);
    crate::leanh::lean_dec(v_x_3544_);
    return v_res_3546_;
}
pub unsafe fn l_Lean_Level_getOffset(
    mut v_lvl_3547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3548_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3549_ = l_Lean_Level_getOffsetAux(v_lvl_3547_, v___x_3548_);
    return v___x_3549_;
}
pub unsafe fn l_Lean_Level_getOffset___boxed(
    mut v_lvl_3550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3551_ = l_Lean_Level_getOffset(v_lvl_3550_);
    crate::leanh::lean_dec(v_lvl_3550_);
    return v_res_3551_;
}
pub unsafe fn l_Lean_Level_getLevelOffset(
    mut v_x_3552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3552_) == 1 {
                    v_a_3553_ = crate::leanh::lean_ctor_get(v_x_3552_, 0);
                    v_x_3552_ = v_a_3553_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_x_3552_);
                    return v_x_3552_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_getLevelOffset___boxed(
    mut v_x_3555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3556_ = l_Lean_Level_getLevelOffset(v_x_3555_);
    crate::leanh::lean_dec(v_x_3555_);
    return v_res_3556_;
}
pub unsafe fn l_Lean_Level_toNat(
    mut v_lvl_3557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = l_Lean_Level_getLevelOffset(v_lvl_3557_);
    if crate::leanh::lean_obj_tag(v___x_3558_) == 0 {
        let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3559_ = l_Lean_Level_getOffset(v_lvl_3557_);
        v___x_3560_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3560_, 0, v___x_3559_);
        return v___x_3560_;
    } else {
        let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3558_);
        v___x_3561_ = crate::leanh::lean_box(0);
        return v___x_3561_;
    }
}
pub unsafe fn l_Lean_Level_toNat___boxed(
    mut v_lvl_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3563_ = l_Lean_Level_toNat(v_lvl_3562_);
    crate::leanh::lean_dec(v_lvl_3562_);
    return v_res_3563_;
}
pub unsafe fn l_Lean_Level_beq___boxed(
    mut v_a_3566_: *mut crate::leanh::LeanObject,
    mut v_b_3567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3568_: u8 = 0;
    let mut v_r_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3568_ = lean_level_eq(v_a_3566_, v_b_3567_);
    crate::leanh::lean_dec(v_b_3567_);
    crate::leanh::lean_dec(v_a_3566_);
    v_r_3569_ = crate::leanh::lean_box((v_res_3568_) as usize);
    return v_r_3569_;
}
pub unsafe fn l_Lean_Level_occurs(
    mut v_x_3572_: *mut crate::leanh::LeanObject,
    mut v_x_3573_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: u8 = 0;
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3580_: u8 = 0;
    let mut v___x_3582_: u8 = 0;
    let mut v___x_3583_: u8 = 0;
    let mut v_a_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: u8 = 0;
    let mut v___x_3589_: u8 = 0;
    let mut v___x_3590_: u8 = 0;
    let mut v___x_3591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3573_) {
                1 => {
                    v_a_3574_ = crate::leanh::lean_ctor_get(v_x_3573_, 0);
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
                    v_a_3577_ = crate::leanh::lean_ctor_get(v_x_3573_, 0);
                    v_a_3578_ = crate::leanh::lean_ctor_get(v_x_3573_, 1);
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
                    v_a_3584_ = crate::leanh::lean_ctor_get(v_x_3573_, 0);
                    v_a_3585_ = crate::leanh::lean_ctor_get(v_x_3573_, 1);
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
    mut v_x_3592_: *mut crate::leanh::LeanObject,
    mut v_x_3593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3594_: u8 = 0;
    let mut v_r_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3594_ = l_Lean_Level_occurs(v_x_3592_, v_x_3593_);
    crate::leanh::lean_dec(v_x_3593_);
    crate::leanh::lean_dec(v_x_3592_);
    v_r_3595_ = crate::leanh::lean_box((v_res_3594_) as usize);
    return v_r_3595_;
}
pub unsafe fn l_Lean_Level_ctorToNat(
    mut v_x_3596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3596_) {
        0 => {
            let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3597_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_3597_;
        }
        1 => {
            let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3598_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_3598_;
        }
        2 => {
            let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3599_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_3599_;
        }
        3 => {
            let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3600_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_3600_;
        }
        4 => {
            let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3601_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_3601_;
        }
        _ => {
            let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3602_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_3602_;
        }
    }
}
pub unsafe fn l_Lean_Level_ctorToNat___boxed(
    mut v_x_3603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3604_ = l_Lean_Level_ctorToNat(v_x_3603_);
    crate::leanh::lean_dec(v_x_3603_);
    return v_res_3604_;
}
pub unsafe fn l_Lean_Level_normLtAux(
    mut v_x_3605_: *mut crate::leanh::LeanObject,
    mut v_x_3606_: *mut crate::leanh::LeanObject,
    mut v_x_3607_: *mut crate::leanh::LeanObject,
    mut v_x_3608_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_l_u2081_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2081_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2081_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_u2082_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: u8 = 0;
    let mut v___x_3626_: u8 = 0;
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: u8 = 0;
    let mut v_a_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: u8 = 0;
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: u8 = 0;
    let mut v_a_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut v___x_3662_: u8 = 0;
    let mut v_a_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: u8 = 0;
    let mut v___x_3668_: u8 = 0;
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3605_) {
                1 => {
                    v_a_3627_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                    v___x_3628_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3629_ = lean_nat_add(v_x_3606_, v___x_3628_);
                    crate::leanh::lean_dec(v_x_3606_);
                    v_x_3605_ = v_a_3627_;
                    v_x_3606_ = v___x_3629_;
                    state = 0;
                    continue;
                }
                2 => match crate::leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3631_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3631_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    2 => {
                        v_a_3632_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3633_ = crate::leanh::lean_ctor_get(v_x_3605_, 1);
                        v_a_3634_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_a_3635_ = crate::leanh::lean_ctor_get(v_x_3607_, 1);
                        v___x_3639_ = lean_level_eq(v_x_3605_, v_x_3607_);
                        if v___x_3639_ == 0 {
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
                            v___x_3640_ = lean_level_eq(v_a_3632_, v_a_3634_);
                            if v___x_3640_ == 0 {
                                state = 3;
                                continue;
                            } else {
                                if v___x_3639_ == 0 {
                                    v___x_3641_ = crate::leanh::lean_unsigned_to_nat(0);
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
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
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
                3 => match crate::leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3644_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3644_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    3 => {
                        v_a_3645_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3646_ = crate::leanh::lean_ctor_get(v_x_3605_, 1);
                        v_a_3647_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_a_3648_ = crate::leanh::lean_ctor_get(v_x_3607_, 1);
                        v___x_3652_ = lean_level_eq(v_x_3605_, v_x_3607_);
                        if v___x_3652_ == 0 {
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
                            v___x_3653_ = lean_level_eq(v_a_3645_, v_a_3647_);
                            if v___x_3653_ == 0 {
                                state = 4;
                                continue;
                            } else {
                                if v___x_3652_ == 0 {
                                    v___x_3654_ = crate::leanh::lean_unsigned_to_nat(0);
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
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
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
                4 => match crate::leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3657_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3657_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    4 => {
                        v_a_3658_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3659_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v___x_3660_ = lean_name_eq(v_a_3658_, v_a_3659_);
                        if v___x_3660_ == 0 {
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
                            v___x_3661_ = l_Lean_Name_lt(v_a_3658_, v_a_3659_);
                            return v___x_3661_;
                        } else {
                            v___x_3662_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
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
                5 => match crate::leanh::lean_obj_tag(v_x_3607_) {
                    1 => {
                        v_a_3663_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v_l_u2081_3610_ = v_x_3605_;
                        v_k_u2081_3611_ = v_x_3606_;
                        v_l_u2082_3612_ = v_a_3663_;
                        v_k_u2082_3613_ = v_x_3608_;
                        state = 1;
                        continue;
                    }
                    5 => {
                        v_a_3664_ = crate::leanh::lean_ctor_get(v_x_3605_, 0);
                        v_a_3665_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
                        v___x_3666_ = lean_name_eq(v_a_3664_, v_a_3665_);
                        if v___x_3666_ == 0 {
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
                            v___x_3667_ = l_Lean_Name_lt(v_a_3664_, v_a_3665_);
                            return v___x_3667_;
                        } else {
                            v___x_3668_ = lean_nat_dec_lt(v_x_3606_, v_x_3608_);
                            crate::leanh::lean_dec(v_x_3608_);
                            crate::leanh::lean_dec(v_x_3606_);
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
                    if crate::leanh::lean_obj_tag(v_x_3607_) == 1 {
                        v_a_3669_ = crate::leanh::lean_ctor_get(v_x_3607_, 0);
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
                v___x_3614_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3615_ = lean_nat_add(v_k_u2082_3613_, v___x_3614_);
                crate::leanh::lean_dec(v_k_u2082_3613_);
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
                    crate::leanh::lean_dec(v_k_u2082_3621_);
                    crate::leanh::lean_dec(v_k_u2081_3619_);
                    v___x_3623_ = l_Lean_Level_ctorToNat(v_l_u2081_3618_);
                    v___x_3624_ = l_Lean_Level_ctorToNat(v_l_u2082_3620_);
                    v___x_3625_ = lean_nat_dec_lt(v___x_3623_, v___x_3624_);
                    crate::leanh::lean_dec(v___x_3624_);
                    crate::leanh::lean_dec(v___x_3623_);
                    return v___x_3625_;
                } else {
                    v___x_3626_ = lean_nat_dec_lt(v_k_u2081_3619_, v_k_u2082_3621_);
                    crate::leanh::lean_dec(v_k_u2082_3621_);
                    crate::leanh::lean_dec(v_k_u2081_3619_);
                    return v___x_3626_;
                }
            }
            3 => {
                v___x_3637_ = crate::leanh::lean_unsigned_to_nat(0);
                v_x_3605_ = v_a_3632_;
                v_x_3606_ = v___x_3637_;
                v_x_3607_ = v_a_3634_;
                v_x_3608_ = v___x_3637_;
                state = 0;
                continue;
            }
            4 => {
                v___x_3650_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_x_3670_: *mut crate::leanh::LeanObject,
    mut v_x_3671_: *mut crate::leanh::LeanObject,
    mut v_x_3672_: *mut crate::leanh::LeanObject,
    mut v_x_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3674_: u8 = 0;
    let mut v_r_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Lean_Level_normLtAux(v_x_3670_, v_x_3671_, v_x_3672_, v_x_3673_);
    crate::leanh::lean_dec(v_x_3672_);
    crate::leanh::lean_dec(v_x_3670_);
    v_r_3675_ = crate::leanh::lean_box((v_res_3674_) as usize);
    return v_r_3675_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter___redArg(
    mut v_x_3676_: *mut crate::leanh::LeanObject,
    mut v_x_3677_: *mut crate::leanh::LeanObject,
    mut v_x_3678_: *mut crate::leanh::LeanObject,
    mut v_x_3679_: *mut crate::leanh::LeanObject,
    mut v_h__1_3680_: *mut crate::leanh::LeanObject,
    mut v_h__2_3681_: *mut crate::leanh::LeanObject,
    mut v_h__3_3682_: *mut crate::leanh::LeanObject,
    mut v_h__4_3683_: *mut crate::leanh::LeanObject,
    mut v_h__5_3684_: *mut crate::leanh::LeanObject,
    mut v_h__6_3685_: *mut crate::leanh::LeanObject,
    mut v_h__7_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3676_) {
        1 => {
            let mut v_a_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_3686_);
            crate::leanh::lean_dec(v_h__6_3685_);
            crate::leanh::lean_dec(v_h__5_3684_);
            crate::leanh::lean_dec(v_h__4_3683_);
            crate::leanh::lean_dec(v_h__3_3682_);
            crate::leanh::lean_dec(v_h__2_3681_);
            v_a_3687_ = crate::leanh::lean_ctor_get(v_x_3676_, 0);
            crate::leanh::lean_inc(v_a_3687_);
            crate::leanh::lean_dec_ref_known(v_x_3676_, 1);
            v___x_3688_ = crate::leanh::lean_apply_4(
                v_h__1_3680_,
                v_a_3687_,
                v_x_3677_,
                v_x_3678_,
                v_x_3679_,
            );
            return v___x_3688_;
        }
        2 => {
            crate::leanh::lean_dec(v_h__6_3685_);
            crate::leanh::lean_dec(v_h__5_3684_);
            crate::leanh::lean_dec(v_h__4_3683_);
            crate::leanh::lean_dec(v_h__1_3680_);
            match crate::leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__3_3682_);
                    v_a_3689_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3689_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3690_ = crate::leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3689_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3690_;
                }
                2 => {
                    let mut v_a_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v_a_3691_ = crate::leanh::lean_ctor_get(v_x_3676_, 0);
                    crate::leanh::lean_inc(v_a_3691_);
                    v_a_3692_ = crate::leanh::lean_ctor_get(v_x_3676_, 1);
                    crate::leanh::lean_inc(v_a_3692_);
                    crate::leanh::lean_dec_ref_known(v_x_3676_, 2);
                    v_a_3693_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3693_);
                    v_a_3694_ = crate::leanh::lean_ctor_get(v_x_3678_, 1);
                    crate::leanh::lean_inc(v_a_3694_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 2);
                    v___x_3695_ = crate::leanh::lean_apply_6(
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
                    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_3682_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v___x_3696_ = crate::leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3696_;
                }
            }
        }
        3 => {
            crate::leanh::lean_dec(v_h__6_3685_);
            crate::leanh::lean_dec(v_h__5_3684_);
            crate::leanh::lean_dec(v_h__3_3682_);
            crate::leanh::lean_dec(v_h__1_3680_);
            match crate::leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__4_3683_);
                    v_a_3697_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3697_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3698_ = crate::leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3697_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3698_;
                }
                3 => {
                    let mut v_a_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v_a_3699_ = crate::leanh::lean_ctor_get(v_x_3676_, 0);
                    crate::leanh::lean_inc(v_a_3699_);
                    v_a_3700_ = crate::leanh::lean_ctor_get(v_x_3676_, 1);
                    crate::leanh::lean_inc(v_a_3700_);
                    crate::leanh::lean_dec_ref_known(v_x_3676_, 2);
                    v_a_3701_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3701_);
                    v_a_3702_ = crate::leanh::lean_ctor_get(v_x_3678_, 1);
                    crate::leanh::lean_inc(v_a_3702_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 2);
                    v___x_3703_ = crate::leanh::lean_apply_6(
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
                    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_3683_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v___x_3704_ = crate::leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3704_;
                }
            }
        }
        4 => {
            crate::leanh::lean_dec(v_h__6_3685_);
            crate::leanh::lean_dec(v_h__4_3683_);
            crate::leanh::lean_dec(v_h__3_3682_);
            crate::leanh::lean_dec(v_h__1_3680_);
            match crate::leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__5_3684_);
                    v_a_3705_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3705_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3706_ = crate::leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3705_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3706_;
                }
                4 => {
                    let mut v_a_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v_a_3707_ = crate::leanh::lean_ctor_get(v_x_3676_, 0);
                    crate::leanh::lean_inc(v_a_3707_);
                    crate::leanh::lean_dec_ref_known(v_x_3676_, 1);
                    v_a_3708_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3708_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3709_ = crate::leanh::lean_apply_4(
                        v_h__5_3684_,
                        v_a_3707_,
                        v_x_3677_,
                        v_a_3708_,
                        v_x_3679_,
                    );
                    return v___x_3709_;
                }
                _ => {
                    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_3684_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v___x_3710_ = crate::leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3710_;
                }
            }
        }
        5 => {
            crate::leanh::lean_dec(v_h__5_3684_);
            crate::leanh::lean_dec(v_h__4_3683_);
            crate::leanh::lean_dec(v_h__3_3682_);
            crate::leanh::lean_dec(v_h__1_3680_);
            match crate::leanh::lean_obj_tag(v_x_3678_) {
                1 => {
                    let mut v_a_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__6_3685_);
                    v_a_3711_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3711_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3712_ = crate::leanh::lean_apply_5(
                        v_h__2_3681_,
                        v_x_3676_,
                        v_x_3677_,
                        v_a_3711_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3712_;
                }
                5 => {
                    let mut v_a_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3686_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v_a_3713_ = crate::leanh::lean_ctor_get(v_x_3676_, 0);
                    crate::leanh::lean_inc(v_a_3713_);
                    crate::leanh::lean_dec_ref_known(v_x_3676_, 1);
                    v_a_3714_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                    crate::leanh::lean_inc(v_a_3714_);
                    crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                    v___x_3715_ = crate::leanh::lean_apply_4(
                        v_h__6_3685_,
                        v_a_3713_,
                        v_x_3677_,
                        v_a_3714_,
                        v_x_3679_,
                    );
                    return v___x_3715_;
                }
                _ => {
                    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_3685_);
                    crate::leanh::lean_dec(v_h__2_3681_);
                    v___x_3716_ = crate::leanh::lean_apply_10(
                        v_h__7_3686_,
                        v_x_3676_,
                        v_x_3677_,
                        v_x_3678_,
                        v_x_3679_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3716_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__6_3685_);
            crate::leanh::lean_dec(v_h__5_3684_);
            crate::leanh::lean_dec(v_h__4_3683_);
            crate::leanh::lean_dec(v_h__3_3682_);
            crate::leanh::lean_dec(v_h__1_3680_);
            if crate::leanh::lean_obj_tag(v_x_3678_) == 1 {
                let mut v_a_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_3686_);
                v_a_3717_ = crate::leanh::lean_ctor_get(v_x_3678_, 0);
                crate::leanh::lean_inc(v_a_3717_);
                crate::leanh::lean_dec_ref_known(v_x_3678_, 1);
                v___x_3718_ = crate::leanh::lean_apply_5(
                    v_h__2_3681_,
                    v_x_3676_,
                    v_x_3677_,
                    v_a_3717_,
                    v_x_3679_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3718_;
            } else {
                let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_3681_);
                v___x_3719_ = crate::leanh::lean_apply_10(
                    v_h__7_3686_,
                    v_x_3676_,
                    v_x_3677_,
                    v_x_3678_,
                    v_x_3679_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3719_;
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_normLtAux_match__1_splitter(
    mut v_motive_3720_: *mut crate::leanh::LeanObject,
    mut v_x_3721_: *mut crate::leanh::LeanObject,
    mut v_x_3722_: *mut crate::leanh::LeanObject,
    mut v_x_3723_: *mut crate::leanh::LeanObject,
    mut v_x_3724_: *mut crate::leanh::LeanObject,
    mut v_h__1_3725_: *mut crate::leanh::LeanObject,
    mut v_h__2_3726_: *mut crate::leanh::LeanObject,
    mut v_h__3_3727_: *mut crate::leanh::LeanObject,
    mut v_h__4_3728_: *mut crate::leanh::LeanObject,
    mut v_h__5_3729_: *mut crate::leanh::LeanObject,
    mut v_h__6_3730_: *mut crate::leanh::LeanObject,
    mut v_h__7_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_3721_) {
        1 => {
            let mut v_a_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__7_3731_);
            crate::leanh::lean_dec(v_h__6_3730_);
            crate::leanh::lean_dec(v_h__5_3729_);
            crate::leanh::lean_dec(v_h__4_3728_);
            crate::leanh::lean_dec(v_h__3_3727_);
            crate::leanh::lean_dec(v_h__2_3726_);
            v_a_3732_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
            crate::leanh::lean_inc(v_a_3732_);
            crate::leanh::lean_dec_ref_known(v_x_3721_, 1);
            v___x_3733_ = crate::leanh::lean_apply_4(
                v_h__1_3725_,
                v_a_3732_,
                v_x_3722_,
                v_x_3723_,
                v_x_3724_,
            );
            return v___x_3733_;
        }
        2 => {
            crate::leanh::lean_dec(v_h__6_3730_);
            crate::leanh::lean_dec(v_h__5_3729_);
            crate::leanh::lean_dec(v_h__4_3728_);
            crate::leanh::lean_dec(v_h__1_3725_);
            match crate::leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__3_3727_);
                    v_a_3734_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3734_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3735_ = crate::leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3734_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3735_;
                }
                2 => {
                    let mut v_a_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v_a_3736_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
                    crate::leanh::lean_inc(v_a_3736_);
                    v_a_3737_ = crate::leanh::lean_ctor_get(v_x_3721_, 1);
                    crate::leanh::lean_inc(v_a_3737_);
                    crate::leanh::lean_dec_ref_known(v_x_3721_, 2);
                    v_a_3738_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3738_);
                    v_a_3739_ = crate::leanh::lean_ctor_get(v_x_3723_, 1);
                    crate::leanh::lean_inc(v_a_3739_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 2);
                    v___x_3740_ = crate::leanh::lean_apply_6(
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
                    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__3_3727_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v___x_3741_ = crate::leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3741_;
                }
            }
        }
        3 => {
            crate::leanh::lean_dec(v_h__6_3730_);
            crate::leanh::lean_dec(v_h__5_3729_);
            crate::leanh::lean_dec(v_h__3_3727_);
            crate::leanh::lean_dec(v_h__1_3725_);
            match crate::leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__4_3728_);
                    v_a_3742_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3742_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3743_ = crate::leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3742_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3743_;
                }
                3 => {
                    let mut v_a_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v_a_3744_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
                    crate::leanh::lean_inc(v_a_3744_);
                    v_a_3745_ = crate::leanh::lean_ctor_get(v_x_3721_, 1);
                    crate::leanh::lean_inc(v_a_3745_);
                    crate::leanh::lean_dec_ref_known(v_x_3721_, 2);
                    v_a_3746_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3746_);
                    v_a_3747_ = crate::leanh::lean_ctor_get(v_x_3723_, 1);
                    crate::leanh::lean_inc(v_a_3747_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 2);
                    v___x_3748_ = crate::leanh::lean_apply_6(
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
                    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_3728_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v___x_3749_ = crate::leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3749_;
                }
            }
        }
        4 => {
            crate::leanh::lean_dec(v_h__6_3730_);
            crate::leanh::lean_dec(v_h__4_3728_);
            crate::leanh::lean_dec(v_h__3_3727_);
            crate::leanh::lean_dec(v_h__1_3725_);
            match crate::leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__5_3729_);
                    v_a_3750_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3750_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3751_ = crate::leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3750_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3751_;
                }
                4 => {
                    let mut v_a_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v_a_3752_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
                    crate::leanh::lean_inc(v_a_3752_);
                    crate::leanh::lean_dec_ref_known(v_x_3721_, 1);
                    v_a_3753_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3753_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3754_ = crate::leanh::lean_apply_4(
                        v_h__5_3729_,
                        v_a_3752_,
                        v_x_3722_,
                        v_a_3753_,
                        v_x_3724_,
                    );
                    return v___x_3754_;
                }
                _ => {
                    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_3729_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v___x_3755_ = crate::leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3755_;
                }
            }
        }
        5 => {
            crate::leanh::lean_dec(v_h__5_3729_);
            crate::leanh::lean_dec(v_h__4_3728_);
            crate::leanh::lean_dec(v_h__3_3727_);
            crate::leanh::lean_dec(v_h__1_3725_);
            match crate::leanh::lean_obj_tag(v_x_3723_) {
                1 => {
                    let mut v_a_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__6_3730_);
                    v_a_3756_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3756_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3757_ = crate::leanh::lean_apply_5(
                        v_h__2_3726_,
                        v_x_3721_,
                        v_x_3722_,
                        v_a_3756_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3757_;
                }
                5 => {
                    let mut v_a_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_3731_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v_a_3758_ = crate::leanh::lean_ctor_get(v_x_3721_, 0);
                    crate::leanh::lean_inc(v_a_3758_);
                    crate::leanh::lean_dec_ref_known(v_x_3721_, 1);
                    v_a_3759_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                    crate::leanh::lean_inc(v_a_3759_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                    v___x_3760_ = crate::leanh::lean_apply_4(
                        v_h__6_3730_,
                        v_a_3758_,
                        v_x_3722_,
                        v_a_3759_,
                        v_x_3724_,
                    );
                    return v___x_3760_;
                }
                _ => {
                    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_3730_);
                    crate::leanh::lean_dec(v_h__2_3726_);
                    v___x_3761_ = crate::leanh::lean_apply_10(
                        v_h__7_3731_,
                        v_x_3721_,
                        v_x_3722_,
                        v_x_3723_,
                        v_x_3724_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3761_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__6_3730_);
            crate::leanh::lean_dec(v_h__5_3729_);
            crate::leanh::lean_dec(v_h__4_3728_);
            crate::leanh::lean_dec(v_h__3_3727_);
            crate::leanh::lean_dec(v_h__1_3725_);
            if crate::leanh::lean_obj_tag(v_x_3723_) == 1 {
                let mut v_a_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__7_3731_);
                v_a_3762_ = crate::leanh::lean_ctor_get(v_x_3723_, 0);
                crate::leanh::lean_inc(v_a_3762_);
                crate::leanh::lean_dec_ref_known(v_x_3723_, 1);
                v___x_3763_ = crate::leanh::lean_apply_5(
                    v_h__2_3726_,
                    v_x_3721_,
                    v_x_3722_,
                    v_a_3762_,
                    v_x_3724_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3763_;
            } else {
                let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_3726_);
                v___x_3764_ = crate::leanh::lean_apply_10(
                    v_h__7_3731_,
                    v_x_3721_,
                    v_x_3722_,
                    v_x_3723_,
                    v_x_3724_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_3764_;
            }
        }
    }
}
pub unsafe fn l_Lean_Level_normLt(
    mut v_l_u2081_3765_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3766_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: u8 = 0;
    v___x_3767_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3768_ =
        l_Lean_Level_normLtAux(v_l_u2081_3765_, v___x_3767_, v_l_u2082_3766_, v___x_3767_);
    return v___x_3768_;
}
pub unsafe fn l_Lean_Level_normLt___boxed(
    mut v_l_u2081_3769_: *mut crate::leanh::LeanObject,
    mut v_l_u2082_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: u8 = 0;
    let mut v_r_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l_Lean_Level_normLt(v_l_u2081_3769_, v_l_u2082_3770_);
    crate::leanh::lean_dec(v_l_u2082_3770_);
    crate::leanh::lean_dec(v_l_u2081_3769_);
    v_r_3772_ = crate::leanh::lean_box((v_res_3771_) as usize);
    return v_r_3772_;
}
pub unsafe fn l_Lean_Level_isAlreadyNormalizedCheap(
    mut v_x_3773_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3774_: u8 = 0;
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: u8 = 0;
    let mut v_a_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_3773_) {
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
                    v_a_3777_ = crate::leanh::lean_ctor_get(v_x_3773_, 0);
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
    mut v_x_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3781_: u8 = 0;
    let mut v_r_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Lean_Level_isAlreadyNormalizedCheap(v_x_3780_);
    crate::leanh::lean_dec(v_x_3780_);
    v_r_3782_ = crate::leanh::lean_box((v_res_3781_) as usize);
    return v_r_3782_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_mkIMaxAux(
    mut v_x_3783_: *mut crate::leanh::LeanObject,
    mut v_x_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_u2081_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_u2082_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3784_) == 0 {
                    crate::leanh::lean_dec(v_x_3783_);
                    return v_x_3784_;
                } else {
                    match crate::leanh::lean_obj_tag(v_x_3783_) {
                        0 => {
                            return v_x_3784_;
                        }
                        1 => {
                            v_a_3790_ = crate::leanh::lean_ctor_get(v_x_3783_, 0);
                            if crate::leanh::lean_obj_tag(v_a_3790_) == 0 {
                                crate::leanh::lean_dec_ref_known(v_x_3783_, 1);
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
                    crate::leanh::lean_dec(v_u_u2082_3787_);
                    return v_u_u2081_3786_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(
    mut v_normalize_3791_: *mut crate::leanh::LeanObject,
    mut v_x_3792_: *mut crate::leanh::LeanObject,
    mut v_x_3793_: u8,
    mut v_x_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3792_) == 2 {
                    v_a_3795_ = crate::leanh::lean_ctor_get(v_x_3792_, 0);
                    crate::leanh::lean_inc(v_a_3795_);
                    v_a_3796_ = crate::leanh::lean_ctor_get(v_x_3792_, 1);
                    crate::leanh::lean_inc(v_a_3796_);
                    crate::leanh::lean_dec_ref_known(v_x_3792_, 2);
                    crate::leanh::lean_inc_ref(v_normalize_3791_);
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
                        crate::leanh::lean_inc_ref(v_normalize_3791_);
                        v___x_3799_ = crate::leanh::lean_apply_1(v_normalize_3791_, v_x_3792_);
                        v___x_3800_ = 1;
                        v_x_3792_ = v___x_3799_;
                        v_x_3793_ = v___x_3800_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_normalize_3791_);
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
    mut v_normalize_3803_: *mut crate::leanh::LeanObject,
    mut v_x_3804_: *mut crate::leanh::LeanObject,
    mut v_x_3805_: *mut crate::leanh::LeanObject,
    mut v_x_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_3807_: u8 = 0;
    let mut v_res_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_3807_ = (crate::leanh::lean_unbox(v_x_3805_) as u8);
    v_res_3808_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux(
        v_normalize_3803_,
        v_x_3804_,
        v_x_36__boxed_3807_,
        v_x_3806_,
    );
    return v_res_3808_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_accMax(
    mut v_result_3809_: *mut crate::leanh::LeanObject,
    mut v_prev_3810_: *mut crate::leanh::LeanObject,
    mut v_offset_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3812_: u8 = 0;
    v___x_3812_ = l_Lean_Level_isZero(v_result_3809_);
    if v___x_3812_ == 0 {
        let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3813_ = l_Lean_Level_addOffsetAux(v_offset_3811_, v_prev_3810_);
        v___x_3814_ = l_Lean_Level_max___override(v_result_3809_, v___x_3813_);
        return v___x_3814_;
    } else {
        let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_result_3809_);
        v___x_3815_ = l_Lean_Level_addOffsetAux(v_offset_3811_, v_prev_3810_);
        return v___x_3815_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_mkMaxAux(
    mut v_lvls_3816_: *mut crate::leanh::LeanObject,
    mut v_extraK_3817_: *mut crate::leanh::LeanObject,
    mut v_i_3818_: *mut crate::leanh::LeanObject,
    mut v_prev_3819_: *mut crate::leanh::LeanObject,
    mut v_prevK_3820_: *mut crate::leanh::LeanObject,
    mut v_result_3821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_curr_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currK_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u8 = 0;
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3822_ = lean_array_get_size(v_lvls_3816_);
                v___x_3823_ = lean_nat_dec_lt(v_i_3818_, v___x_3822_);
                if v___x_3823_ == 0 {
                    crate::leanh::lean_dec(v_i_3818_);
                    v___x_3824_ = lean_nat_add(v_extraK_3817_, v_prevK_3820_);
                    crate::leanh::lean_dec(v_prevK_3820_);
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
                        v___x_3830_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3831_ = lean_nat_add(v_i_3818_, v___x_3830_);
                        crate::leanh::lean_dec(v_i_3818_);
                        v___x_3832_ = lean_nat_add(v_extraK_3817_, v_prevK_3820_);
                        crate::leanh::lean_dec(v_prevK_3820_);
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
                        crate::leanh::lean_dec(v_prevK_3820_);
                        crate::leanh::lean_dec(v_prev_3819_);
                        v___x_3835_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3836_ = lean_nat_add(v_i_3818_, v___x_3835_);
                        crate::leanh::lean_dec(v_i_3818_);
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
    mut v_lvls_3838_: *mut crate::leanh::LeanObject,
    mut v_extraK_3839_: *mut crate::leanh::LeanObject,
    mut v_i_3840_: *mut crate::leanh::LeanObject,
    mut v_prev_3841_: *mut crate::leanh::LeanObject,
    mut v_prevK_3842_: *mut crate::leanh::LeanObject,
    mut v_result_3843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3844_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(
        v_lvls_3838_,
        v_extraK_3839_,
        v_i_3840_,
        v_prev_3841_,
        v_prevK_3842_,
        v_result_3843_,
    );
    crate::leanh::lean_dec(v_extraK_3839_);
    crate::leanh::lean_dec_ref(v_lvls_3838_);
    return v_res_3844_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_skipExplicit(
    mut v_lvls_3845_: *mut crate::leanh::LeanObject,
    mut v_i_3846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: u8 = 0;
    let mut v_lvl_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v___x_3850_);
                    if v___x_3851_ == 0 {
                        return v_i_3846_;
                    } else {
                        v___x_3852_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3853_ = lean_nat_add(v_i_3846_, v___x_3852_);
                        crate::leanh::lean_dec(v_i_3846_);
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
    mut v_lvls_3855_: *mut crate::leanh::LeanObject,
    mut v_i_3856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3857_ = l___private_Lean_Level_0__Lean_Level_skipExplicit(v_lvls_3855_, v_i_3856_);
    crate::leanh::lean_dec_ref(v_lvls_3855_);
    return v_res_3857_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
    mut v_lvls_3858_: *mut crate::leanh::LeanObject,
    mut v_maxExplicit_3859_: *mut crate::leanh::LeanObject,
    mut v_i_3860_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: u8 = 0;
    let mut v_lvl_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: u8 = 0;
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3861_ = lean_array_get_size(v_lvls_3858_);
                v___x_3862_ = lean_nat_dec_lt(v_i_3860_, v___x_3861_);
                if v___x_3862_ == 0 {
                    crate::leanh::lean_dec(v_i_3860_);
                    return v___x_3862_;
                } else {
                    v_lvl_3863_ = lean_array_fget_borrowed(v_lvls_3858_, v_i_3860_);
                    v___x_3864_ = l_Lean_Level_getOffset(v_lvl_3863_);
                    v___x_3865_ = lean_nat_dec_le(v_maxExplicit_3859_, v___x_3864_);
                    crate::leanh::lean_dec(v___x_3864_);
                    if v___x_3865_ == 0 {
                        v___x_3866_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3867_ = lean_nat_add(v_i_3860_, v___x_3866_);
                        crate::leanh::lean_dec(v_i_3860_);
                        v_i_3860_ = v___x_3867_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_3860_);
                        return v___x_3865_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux___boxed(
    mut v_lvls_3869_: *mut crate::leanh::LeanObject,
    mut v_maxExplicit_3870_: *mut crate::leanh::LeanObject,
    mut v_i_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3872_: u8 = 0;
    let mut v_r_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3872_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
        v_lvls_3869_,
        v_maxExplicit_3870_,
        v_i_3871_,
    );
    crate::leanh::lean_dec(v_maxExplicit_3870_);
    crate::leanh::lean_dec_ref(v_lvls_3869_);
    v_r_3873_ = crate::leanh::lean_box((v_res_3872_) as usize);
    return v_r_3873_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
    mut v_lvls_3874_: *mut crate::leanh::LeanObject,
    mut v_firstNonExplicit_3875_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: u8 = 0;
    v___x_3876_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3877_ = lean_nat_dec_eq(v_firstNonExplicit_3875_, v___x_3876_);
    if v___x_3877_ == 0 {
        let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_max_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3883_: u8 = 0;
        v___x_3878_ = crate::leanh::lean_box(0);
        v___x_3879_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_3880_ = lean_nat_sub(v_firstNonExplicit_3875_, v___x_3879_);
        v___x_3881_ = lean_array_get_borrowed(v___x_3878_, v_lvls_3874_, v___x_3880_);
        crate::leanh::lean_dec(v___x_3880_);
        v_max_3882_ = l_Lean_Level_getOffset(v___x_3881_);
        v___x_3883_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumedAux(
            v_lvls_3874_,
            v_max_3882_,
            v_firstNonExplicit_3875_,
        );
        crate::leanh::lean_dec(v_max_3882_);
        return v___x_3883_;
    } else {
        let mut v___x_3884_: u8 = 0;
        crate::leanh::lean_dec(v_firstNonExplicit_3875_);
        v___x_3884_ = 0;
        return v___x_3884_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed___boxed(
    mut v_lvls_3885_: *mut crate::leanh::LeanObject,
    mut v_firstNonExplicit_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3887_: u8 = 0;
    let mut v_r_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3887_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
        v_lvls_3885_,
        v_firstNonExplicit_3886_,
    );
    crate::leanh::lean_dec_ref(v_lvls_3885_);
    v_r_3888_ = crate::leanh::lean_box((v_res_3887_) as usize);
    return v_r_3888_;
}
pub unsafe fn l_panic___at___00Lean_Level_normalize_spec__2(
    mut v_msg_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3890_ = crate::leanh::lean_box(0);
    v___x_3891_ = lean_panic_fn_borrowed(v___x_3890_, v_msg_3889_);
    return v___x_3891_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(
    mut v_hi_3892_: *mut crate::leanh::LeanObject,
    mut v_pivot_3893_: *mut crate::leanh::LeanObject,
    mut v_as_3894_: *mut crate::leanh::LeanObject,
    mut v_i_3895_: *mut crate::leanh::LeanObject,
    mut v_k_3896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3897_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: u8 = 0;
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3897_ = lean_nat_dec_lt(v_k_3896_, v_hi_3892_);
                if v___x_3897_ == 0 {
                    crate::leanh::lean_dec(v_k_3896_);
                    v___x_3898_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_hi_3892_);
                    v___x_3899_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3899_, 0, v_i_3895_);
                    crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3898_);
                    return v___x_3899_;
                } else {
                    v___x_3900_ = lean_array_fget_borrowed(v_as_3894_, v_k_3896_);
                    v___x_3901_ = l_Lean_Level_normLt(v___x_3900_, v_pivot_3893_);
                    if v___x_3901_ == 0 {
                        v___x_3902_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3903_ = lean_nat_add(v_k_3896_, v___x_3902_);
                        crate::leanh::lean_dec(v_k_3896_);
                        v_k_3896_ = v___x_3903_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3905_ = lean_array_fswap(v_as_3894_, v_i_3895_, v_k_3896_);
                        v___x_3906_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3907_ = lean_nat_add(v_i_3895_, v___x_3906_);
                        crate::leanh::lean_dec(v_i_3895_);
                        v___x_3908_ = lean_nat_add(v_k_3896_, v___x_3906_);
                        crate::leanh::lean_dec(v_k_3896_);
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
    mut v_hi_3910_: *mut crate::leanh::LeanObject,
    mut v_pivot_3911_: *mut crate::leanh::LeanObject,
    mut v_as_3912_: *mut crate::leanh::LeanObject,
    mut v_i_3913_: *mut crate::leanh::LeanObject,
    mut v_k_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3915_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_3910_, v_pivot_3911_, v_as_3912_, v_i_3913_, v_k_3914_);
    crate::leanh::lean_dec(v_pivot_3911_);
    crate::leanh::lean_dec(v_hi_3910_);
    return v_res_3915_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(
    mut v_n_3916_: *mut crate::leanh::LeanObject,
    mut v_as_3917_: *mut crate::leanh::LeanObject,
    mut v_lo_3918_: *mut crate::leanh::LeanObject,
    mut v_hi_3919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: u8 = 0;
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: u8 = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3931_ = lean_nat_dec_lt(v_lo_3918_, v_hi_3919_);
                if v___x_3931_ == 0 {
                    crate::leanh::lean_dec(v_lo_3918_);
                    return v_as_3917_;
                } else {
                    v___x_3932_ = lean_nat_add(v_lo_3918_, v_hi_3919_);
                    v___x_3933_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_3934_ = lean_nat_shiftr(v___x_3932_, v___x_3933_);
                    crate::leanh::lean_dec(v___x_3932_);
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
                crate::leanh::lean_inc_n(v_lo_3918_, 2);
                v___x_3923_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_3919_, v_pivot_3922_, v___y_3921_, v_lo_3918_, v_lo_3918_);
                crate::leanh::lean_dec(v_pivot_3922_);
                v_fst_3924_ = crate::leanh::lean_ctor_get(v___x_3923_, 0);
                crate::leanh::lean_inc(v_fst_3924_);
                v_snd_3925_ = crate::leanh::lean_ctor_get(v___x_3923_, 1);
                crate::leanh::lean_inc(v_snd_3925_);
                crate::leanh::lean_dec_ref(v___x_3923_);
                v___x_3926_ = lean_nat_dec_le(v_hi_3919_, v_fst_3924_);
                if v___x_3926_ == 0 {
                    v___x_3927_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_3916_, v_snd_3925_, v_lo_3918_, v_fst_3924_);
                    v___x_3928_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3929_ = lean_nat_add(v_fst_3924_, v___x_3928_);
                    crate::leanh::lean_dec(v_fst_3924_);
                    v_as_3917_ = v___x_3927_;
                    v_lo_3918_ = v___x_3929_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_3924_);
                    crate::leanh::lean_dec(v_lo_3918_);
                    return v_snd_3925_;
                }
            }
            2 => {
                v___x_3937_ = lean_array_fget_borrowed(v___y_3936_, v_mid_3934_);
                v___x_3938_ = lean_array_fget_borrowed(v___y_3936_, v_hi_3919_);
                v___x_3939_ = l_Lean_Level_normLt(v___x_3937_, v___x_3938_);
                if v___x_3939_ == 0 {
                    crate::leanh::lean_dec(v_mid_3934_);
                    v___y_3921_ = v___y_3936_;
                    state = 1;
                    continue;
                } else {
                    v___x_3940_ = lean_array_fswap(v___y_3936_, v_mid_3934_, v_hi_3919_);
                    crate::leanh::lean_dec(v_mid_3934_);
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
    mut v_n_3951_: *mut crate::leanh::LeanObject,
    mut v_as_3952_: *mut crate::leanh::LeanObject,
    mut v_lo_3953_: *mut crate::leanh::LeanObject,
    mut v_hi_3954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3955_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_3951_, v_as_3952_, v_lo_3953_, v_hi_3954_);
    crate::leanh::lean_dec(v_hi_3954_);
    crate::leanh::lean_dec(v_n_3951_);
    return v_res_3955_;
}
pub unsafe fn _init_l_Lean_Level_normalize___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3960_ = l_Lean_Level_normalize___closed__2;
    v___x_3961_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_3962_ = crate::leanh::lean_unsigned_to_nat(401);
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
    mut v_l_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: u8 = 0;
    let mut v_k_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvls_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvls_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lvl_u2081_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prev_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevK_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_firstNonExplicit_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: u8 = 0;
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: u8 = 0;
    let mut v___x_4001_: u8 = 0;
    let mut v_a_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: u8 = 0;
    let mut v_l_u2081_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3967_ = l_Lean_Level_isAlreadyNormalizedCheap(v_l_3966_);
                if v___x_3967_ == 0 {
                    v_k_3968_ = l_Lean_Level_getOffset(v_l_3966_);
                    v_u_3969_ = l_Lean_Level_getLevelOffset(v_l_3966_);
                    match crate::leanh::lean_obj_tag(v_u_3969_) {
                        2 => {
                            v_a_3970_ = crate::leanh::lean_ctor_get(v_u_3969_, 0);
                            crate::leanh::lean_inc(v_a_3970_);
                            v_a_3971_ = crate::leanh::lean_ctor_get(v_u_3969_, 1);
                            crate::leanh::lean_inc(v_a_3971_);
                            crate::leanh::lean_dec_ref_known(v_u_3969_, 2);
                            v___x_3972_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3973_ = l_Lean_Level_normalize___closed__0;
                            v_lvls_3974_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_3970_, v___x_3967_, v___x_3973_);
                            v_lvls_3975_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_3971_, v___x_3967_, v_lvls_3974_);
                            v___x_3976_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3991_ = lean_array_get_size(v_lvls_3975_);
                            v___x_3996_ = lean_nat_dec_eq(v___x_3991_, v___x_3972_);
                            if v___x_3996_ == 0 {
                                v___x_3997_ = lean_nat_sub(v___x_3991_, v___x_3976_);
                                v___x_4001_ = lean_nat_dec_le(v___x_3972_, v___x_3997_);
                                if v___x_4001_ == 0 {
                                    crate::leanh::lean_inc(v___x_3997_);
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
                            v_a_4002_ = crate::leanh::lean_ctor_get(v_u_3969_, 0);
                            crate::leanh::lean_inc(v_a_4002_);
                            v_a_4003_ = crate::leanh::lean_ctor_get(v_u_3969_, 1);
                            crate::leanh::lean_inc(v_a_4003_);
                            crate::leanh::lean_dec_ref_known(v_u_3969_, 2);
                            v___x_4004_ = l_Lean_Level_isNeverZero(v_a_4003_);
                            if v___x_4004_ == 0 {
                                v_l_u2081_4005_ = l_Lean_Level_normalize(v_a_4002_);
                                crate::leanh::lean_dec(v_a_4002_);
                                v_l_u2082_4006_ = l_Lean_Level_normalize(v_a_4003_);
                                crate::leanh::lean_dec(v_a_4003_);
                                v___x_4007_ = l___private_Lean_Level_0__Lean_Level_mkIMaxAux(
                                    v_l_u2081_4005_,
                                    v_l_u2082_4006_,
                                );
                                v___x_4008_ = l_Lean_Level_addOffsetAux(v_k_3968_, v___x_4007_);
                                return v___x_4008_;
                            } else {
                                v___x_4009_ = l_Lean_Level_max___override(v_a_4002_, v_a_4003_);
                                v___x_4010_ = l_Lean_Level_normalize(v___x_4009_);
                                crate::leanh::lean_dec(v___x_4009_);
                                v___x_4011_ = l_Lean_Level_addOffsetAux(v_k_3968_, v___x_4010_);
                                return v___x_4011_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec(v_u_3969_);
                            crate::leanh::lean_dec(v_k_3968_);
                            v___x_4012_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_inc(v_l_3966_);
                    return v_l_3966_;
                }
            }
            1 => {
                v___x_3980_ = crate::leanh::lean_box(0);
                v_lvl_u2081_3981_ = lean_array_get_borrowed(v___x_3980_, v___y_3978_, v___y_3979_);
                v_prev_3982_ = l_Lean_Level_getLevelOffset(v_lvl_u2081_3981_);
                v_prevK_3983_ = l_Lean_Level_getOffset(v_lvl_u2081_3981_);
                v___x_3984_ = lean_nat_add(v___y_3979_, v___x_3976_);
                crate::leanh::lean_dec(v___y_3979_);
                v___x_3985_ = l___private_Lean_Level_0__Lean_Level_mkMaxAux(
                    v___y_3978_,
                    v_k_3968_,
                    v___x_3984_,
                    v_prev_3982_,
                    v_prevK_3983_,
                    v___x_3980_,
                );
                crate::leanh::lean_dec(v_k_3968_);
                crate::leanh::lean_dec_ref(v___y_3978_);
                return v___x_3985_;
            }
            2 => {
                v_firstNonExplicit_3988_ =
                    l___private_Lean_Level_0__Lean_Level_skipExplicit(v___y_3987_, v___x_3972_);
                crate::leanh::lean_inc(v_firstNonExplicit_3988_);
                v___x_3989_ = l___private_Lean_Level_0__Lean_Level_isExplicitSubsumed(
                    v___y_3987_,
                    v_firstNonExplicit_3988_,
                );
                if v___x_3989_ == 0 {
                    v___x_3990_ = lean_nat_sub(v_firstNonExplicit_3988_, v___x_3976_);
                    crate::leanh::lean_dec(v_firstNonExplicit_3988_);
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
                crate::leanh::lean_dec(v___y_3994_);
                v___y_3987_ = v___x_3995_;
                state = 2;
                continue;
            }
            4 => {
                v___x_4000_ = lean_nat_dec_le(v___y_3999_, v___x_3997_);
                if v___x_4000_ == 0 {
                    crate::leanh::lean_dec(v___x_3997_);
                    crate::leanh::lean_inc(v___y_3999_);
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
    mut v_x_4014_: *mut crate::leanh::LeanObject,
    mut v_x_4015_: u8,
    mut v_x_4016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4014_) == 2 {
                    v_a_4017_ = crate::leanh::lean_ctor_get(v_x_4014_, 0);
                    crate::leanh::lean_inc(v_a_4017_);
                    v_a_4018_ = crate::leanh::lean_ctor_get(v_x_4014_, 1);
                    crate::leanh::lean_inc(v_a_4018_);
                    crate::leanh::lean_dec_ref_known(v_x_4014_, 2);
                    v___x_4019_ = l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(v_a_4017_, v_x_4015_, v_x_4016_);
                    v_x_4014_ = v_a_4018_;
                    v_x_4016_ = v___x_4019_;
                    state = 0;
                    continue;
                } else {
                    if v_x_4015_ == 0 {
                        v___x_4021_ = l_Lean_Level_normalize(v_x_4014_);
                        crate::leanh::lean_dec(v_x_4014_);
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
    mut v_x_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
    mut v_x_4027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_676__boxed_4028_: u8 = 0;
    let mut v_res_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_676__boxed_4028_ = (crate::leanh::lean_unbox(v_x_4026_) as u8);
    v_res_4029_ =
        l___private_Lean_Level_0__Lean_Level_getMaxArgsAux___at___00Lean_Level_normalize_spec__0(
            v_x_4025_,
            v_x_676__boxed_4028_,
            v_x_4027_,
        );
    return v_res_4029_;
}
pub unsafe fn l_Lean_Level_normalize___boxed(
    mut v_l_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Lean_Level_normalize(v_l_4030_);
    crate::leanh::lean_dec(v_l_4030_);
    return v_res_4031_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(
    mut v_n_4032_: *mut crate::leanh::LeanObject,
    mut v_as_4033_: *mut crate::leanh::LeanObject,
    mut v_lo_4034_: *mut crate::leanh::LeanObject,
    mut v_hi_4035_: *mut crate::leanh::LeanObject,
    mut v_w_4036_: *mut crate::leanh::LeanObject,
    mut v_hlo_4037_: *mut crate::leanh::LeanObject,
    mut v_hhi_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4039_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___redArg(v_n_4032_, v_as_4033_, v_lo_4034_, v_hi_4035_);
    return v___x_4039_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1___boxed(
    mut v_n_4040_: *mut crate::leanh::LeanObject,
    mut v_as_4041_: *mut crate::leanh::LeanObject,
    mut v_lo_4042_: *mut crate::leanh::LeanObject,
    mut v_hi_4043_: *mut crate::leanh::LeanObject,
    mut v_w_4044_: *mut crate::leanh::LeanObject,
    mut v_hlo_4045_: *mut crate::leanh::LeanObject,
    mut v_hhi_4046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4047_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1(v_n_4040_, v_as_4041_, v_lo_4042_, v_hi_4043_, v_w_4044_, v_hlo_4045_, v_hhi_4046_);
    crate::leanh::lean_dec(v_hi_4043_);
    crate::leanh::lean_dec(v_n_4040_);
    return v_res_4047_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(
    mut v_n_4048_: *mut crate::leanh::LeanObject,
    mut v_lo_4049_: *mut crate::leanh::LeanObject,
    mut v_hi_4050_: *mut crate::leanh::LeanObject,
    mut v_hhi_4051_: *mut crate::leanh::LeanObject,
    mut v_pivot_4052_: *mut crate::leanh::LeanObject,
    mut v_as_4053_: *mut crate::leanh::LeanObject,
    mut v_i_4054_: *mut crate::leanh::LeanObject,
    mut v_k_4055_: *mut crate::leanh::LeanObject,
    mut v_ilo_4056_: *mut crate::leanh::LeanObject,
    mut v_ik_4057_: *mut crate::leanh::LeanObject,
    mut v_w_4058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4059_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___redArg(v_hi_4050_, v_pivot_4052_, v_as_4053_, v_i_4054_, v_k_4055_);
    return v___x_4059_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1___boxed(
    mut v_n_4060_: *mut crate::leanh::LeanObject,
    mut v_lo_4061_: *mut crate::leanh::LeanObject,
    mut v_hi_4062_: *mut crate::leanh::LeanObject,
    mut v_hhi_4063_: *mut crate::leanh::LeanObject,
    mut v_pivot_4064_: *mut crate::leanh::LeanObject,
    mut v_as_4065_: *mut crate::leanh::LeanObject,
    mut v_i_4066_: *mut crate::leanh::LeanObject,
    mut v_k_4067_: *mut crate::leanh::LeanObject,
    mut v_ilo_4068_: *mut crate::leanh::LeanObject,
    mut v_ik_4069_: *mut crate::leanh::LeanObject,
    mut v_w_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Level_normalize_spec__1_spec__1(v_n_4060_, v_lo_4061_, v_hi_4062_, v_hhi_4063_, v_pivot_4064_, v_as_4065_, v_i_4066_, v_k_4067_, v_ilo_4068_, v_ik_4069_, v_w_4070_);
    crate::leanh::lean_dec(v_pivot_4064_);
    crate::leanh::lean_dec(v_hi_4062_);
    crate::leanh::lean_dec(v_lo_4061_);
    crate::leanh::lean_dec(v_n_4060_);
    return v_res_4071_;
}
pub unsafe fn l_Lean_Level_isEquiv(
    mut v_u_4072_: *mut crate::leanh::LeanObject,
    mut v_v_4073_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4074_: u8 = 0;
    v___x_4074_ = lean_level_eq(v_u_4072_, v_v_4073_);
    if v___x_4074_ == 0 {
        let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4077_: u8 = 0;
        v___x_4075_ = l_Lean_Level_normalize(v_u_4072_);
        v___x_4076_ = l_Lean_Level_normalize(v_v_4073_);
        v___x_4077_ = lean_level_eq(v___x_4075_, v___x_4076_);
        crate::leanh::lean_dec(v___x_4076_);
        crate::leanh::lean_dec(v___x_4075_);
        return v___x_4077_;
    } else {
        return v___x_4074_;
    }
}
pub unsafe fn l_Lean_Level_isEquiv___boxed(
    mut v_u_4078_: *mut crate::leanh::LeanObject,
    mut v_v_4079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4080_: u8 = 0;
    let mut v_r_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4080_ = l_Lean_Level_isEquiv(v_u_4078_, v_v_4079_);
    crate::leanh::lean_dec(v_v_4079_);
    crate::leanh::lean_dec(v_u_4078_);
    v_r_4081_ = crate::leanh::lean_box((v_res_4080_) as usize);
    return v_r_4081_;
}
pub unsafe fn l_Lean_Level_dec(
    mut v_x_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_u2081_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4092_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4082_) {
                0 => {
                    v___x_4098_ = crate::leanh::lean_box(0);
                    return v___x_4098_;
                }
                1 => {
                    v_a_4099_ = crate::leanh::lean_ctor_get(v_x_4082_, 0);
                    crate::leanh::lean_inc(v_a_4099_);
                    v___x_4100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4100_, 0, v_a_4099_);
                    return v___x_4100_;
                }
                2 => {
                    v_a_4101_ = crate::leanh::lean_ctor_get(v_x_4082_, 0);
                    v_a_4102_ = crate::leanh::lean_ctor_get(v_x_4082_, 1);
                    v_l_u2081_4084_ = v_a_4101_;
                    v_l_u2082_4085_ = v_a_4102_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_4103_ = crate::leanh::lean_ctor_get(v_x_4082_, 0);
                    v_a_4104_ = crate::leanh::lean_ctor_get(v_x_4082_, 1);
                    v_l_u2081_4084_ = v_a_4103_;
                    v_l_u2082_4085_ = v_a_4104_;
                    state = 1;
                    continue;
                }
                _ => {
                    v___x_4105_ = crate::leanh::lean_box(0);
                    return v___x_4105_;
                }
            },
            1 => {
                v___x_4086_ = l_Lean_Level_dec(v_l_u2081_4084_);
                if crate::leanh::lean_obj_tag(v___x_4086_) == 0 {
                    return v___x_4086_;
                } else {
                    v_val_4087_ = crate::leanh::lean_ctor_get(v___x_4086_, 0);
                    crate::leanh::lean_inc(v_val_4087_);
                    crate::leanh::lean_dec_ref_known(v___x_4086_, 1);
                    v___x_4088_ = l_Lean_Level_dec(v_l_u2082_4085_);
                    if crate::leanh::lean_obj_tag(v___x_4088_) == 0 {
                        crate::leanh::lean_dec(v_val_4087_);
                        return v___x_4088_;
                    } else {
                        v_val_4089_ = crate::leanh::lean_ctor_get(v___x_4088_, 0);
                        v_isSharedCheck_4097_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4088_)) as u8;
                        if v_isSharedCheck_4097_ == 0 {
                            v___x_4091_ = v___x_4088_;
                            v_isShared_4092_ = v_isSharedCheck_4097_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4089_);
                            crate::leanh::lean_dec(v___x_4088_);
                            v___x_4091_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_ctor_set(v___x_4091_, 0, v___x_4093_);
                    v___x_4095_ = v___x_4091_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4096_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4093_);
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
    mut v_x_4106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4107_ = l_Lean_Level_dec(v_x_4106_);
    crate::leanh::lean_dec(v_x_4106_);
    return v_res_4107_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorIdx(
    mut v_x_4108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_4108_) {
        0 => {
            let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4109_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_4109_;
        }
        1 => {
            let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4110_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_4110_;
        }
        2 => {
            let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4111_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_4111_;
        }
        3 => {
            let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4112_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_4112_;
        }
        _ => {
            let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4113_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_4113_;
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_ctorIdx___boxed(
    mut v_x_4114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4115_ = l_Lean_Level_PP_Result_ctorIdx(v_x_4114_);
    crate::leanh::lean_dec_ref(v_x_4114_);
    return v_res_4115_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim___redArg(
    mut v_t_4116_: *mut crate::leanh::LeanObject,
    mut v_k_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_4116_) == 2 {
        let mut v_a_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4118_ = crate::leanh::lean_ctor_get(v_t_4116_, 0);
        crate::leanh::lean_inc_ref(v_a_4118_);
        v_a_4119_ = crate::leanh::lean_ctor_get(v_t_4116_, 1);
        crate::leanh::lean_inc(v_a_4119_);
        crate::leanh::lean_dec_ref_known(v_t_4116_, 2);
        v___x_4120_ = crate::leanh::lean_apply_2(v_k_4117_, v_a_4118_, v_a_4119_);
        return v___x_4120_;
    } else {
        let mut v_a_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4121_ = crate::leanh::lean_ctor_get(v_t_4116_, 0);
        crate::leanh::lean_inc(v_a_4121_);
        crate::leanh::lean_dec_ref(v_t_4116_);
        v___x_4122_ = crate::leanh::lean_apply_1(v_k_4117_, v_a_4121_);
        return v___x_4122_;
    }
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim(
    mut v_motive__1_4123_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4124_: *mut crate::leanh::LeanObject,
    mut v_t_4125_: *mut crate::leanh::LeanObject,
    mut v_h_4126_: *mut crate::leanh::LeanObject,
    mut v_k_4127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4128_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4125_, v_k_4127_);
    return v___x_4128_;
}
pub unsafe fn l_Lean_Level_PP_Result_ctorElim___boxed(
    mut v_motive__1_4129_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_4130_: *mut crate::leanh::LeanObject,
    mut v_t_4131_: *mut crate::leanh::LeanObject,
    mut v_h_4132_: *mut crate::leanh::LeanObject,
    mut v_k_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4134_ = l_Lean_Level_PP_Result_ctorElim(
        v_motive__1_4129_,
        v_ctorIdx_4130_,
        v_t_4131_,
        v_h_4132_,
        v_k_4133_,
    );
    crate::leanh::lean_dec(v_ctorIdx_4130_);
    return v_res_4134_;
}
pub unsafe fn l_Lean_Level_PP_Result_leaf_elim___redArg(
    mut v_t_4135_: *mut crate::leanh::LeanObject,
    mut v_leaf_4136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4135_, v_leaf_4136_);
    return v___x_4137_;
}
pub unsafe fn l_Lean_Level_PP_Result_leaf_elim(
    mut v_motive__1_4138_: *mut crate::leanh::LeanObject,
    mut v_t_4139_: *mut crate::leanh::LeanObject,
    mut v_h_4140_: *mut crate::leanh::LeanObject,
    mut v_leaf_4141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4142_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4139_, v_leaf_4141_);
    return v___x_4142_;
}
pub unsafe fn l_Lean_Level_PP_Result_num_elim___redArg(
    mut v_t_4143_: *mut crate::leanh::LeanObject,
    mut v_num_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4145_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4143_, v_num_4144_);
    return v___x_4145_;
}
pub unsafe fn l_Lean_Level_PP_Result_num_elim(
    mut v_motive__1_4146_: *mut crate::leanh::LeanObject,
    mut v_t_4147_: *mut crate::leanh::LeanObject,
    mut v_h_4148_: *mut crate::leanh::LeanObject,
    mut v_num_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4150_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4147_, v_num_4149_);
    return v___x_4150_;
}
pub unsafe fn l_Lean_Level_PP_Result_offset_elim___redArg(
    mut v_t_4151_: *mut crate::leanh::LeanObject,
    mut v_offset_4152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4153_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4151_, v_offset_4152_);
    return v___x_4153_;
}
pub unsafe fn l_Lean_Level_PP_Result_offset_elim(
    mut v_motive__1_4154_: *mut crate::leanh::LeanObject,
    mut v_t_4155_: *mut crate::leanh::LeanObject,
    mut v_h_4156_: *mut crate::leanh::LeanObject,
    mut v_offset_4157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4158_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4155_, v_offset_4157_);
    return v___x_4158_;
}
pub unsafe fn l_Lean_Level_PP_Result_maxNode_elim___redArg(
    mut v_t_4159_: *mut crate::leanh::LeanObject,
    mut v_maxNode_4160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4161_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4159_, v_maxNode_4160_);
    return v___x_4161_;
}
pub unsafe fn l_Lean_Level_PP_Result_maxNode_elim(
    mut v_motive__1_4162_: *mut crate::leanh::LeanObject,
    mut v_t_4163_: *mut crate::leanh::LeanObject,
    mut v_h_4164_: *mut crate::leanh::LeanObject,
    mut v_maxNode_4165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4166_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4163_, v_maxNode_4165_);
    return v___x_4166_;
}
pub unsafe fn l_Lean_Level_PP_Result_imaxNode_elim___redArg(
    mut v_t_4167_: *mut crate::leanh::LeanObject,
    mut v_imaxNode_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4169_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4167_, v_imaxNode_4168_);
    return v___x_4169_;
}
pub unsafe fn l_Lean_Level_PP_Result_imaxNode_elim(
    mut v_motive__1_4170_: *mut crate::leanh::LeanObject,
    mut v_t_4171_: *mut crate::leanh::LeanObject,
    mut v_h_4172_: *mut crate::leanh::LeanObject,
    mut v_imaxNode_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l_Lean_Level_PP_Result_ctorElim___redArg(v_t_4171_, v_imaxNode_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Level_PP_Result_succ(
    mut v_x_4175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4180_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut v_a_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4175_) {
                2 => {
                    v_a_4176_ = crate::leanh::lean_ctor_get(v_x_4175_, 0);
                    v_a_4177_ = crate::leanh::lean_ctor_get(v_x_4175_, 1);
                    v_isSharedCheck_4186_ = (!crate::leanh::lean_is_exclusive(v_x_4175_)) as u8;
                    if v_isSharedCheck_4186_ == 0 {
                        v___x_4179_ = v_x_4175_;
                        v_isShared_4180_ = v_isSharedCheck_4186_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4177_);
                        crate::leanh::lean_inc(v_a_4176_);
                        crate::leanh::lean_dec(v_x_4175_);
                        v___x_4179_ = crate::leanh::lean_box(0);
                        v_isShared_4180_ = v_isSharedCheck_4186_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4187_ = crate::leanh::lean_ctor_get(v_x_4175_, 0);
                    v_isSharedCheck_4196_ = (!crate::leanh::lean_is_exclusive(v_x_4175_)) as u8;
                    if v_isSharedCheck_4196_ == 0 {
                        v___x_4189_ = v_x_4175_;
                        v_isShared_4190_ = v_isSharedCheck_4196_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4187_);
                        crate::leanh::lean_dec(v_x_4175_);
                        v___x_4189_ = crate::leanh::lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4196_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_4197_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4198_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4198_, 0, v_x_4175_);
                    crate::leanh::lean_ctor_set(v___x_4198_, 1, v___x_4197_);
                    return v___x_4198_;
                }
            },
            1 => {
                v___x_4181_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4182_ = lean_nat_add(v_a_4177_, v___x_4181_);
                crate::leanh::lean_dec(v_a_4177_);
                if v_isShared_4180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4179_, 1, v___x_4182_);
                    v___x_4184_ = v___x_4179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4185_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 0, v_a_4176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4185_, 1, v___x_4182_);
                    v___x_4184_ = v_reuseFailAlloc_4185_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4184_;
            }
            3 => {
                v___x_4191_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4192_ = lean_nat_add(v_a_4187_, v___x_4191_);
                crate::leanh::lean_dec(v_a_4187_);
                if v_isShared_4190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4189_, 0, v___x_4192_);
                    v___x_4194_ = v___x_4189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4195_, 0, v___x_4192_);
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
    mut v_x_4199_: *mut crate::leanh::LeanObject,
    mut v_x_4200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4204_: u8 = 0;
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4209_: u8 = 0;
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4200_) == 3 {
                    v_a_4201_ = crate::leanh::lean_ctor_get(v_x_4200_, 0);
                    v_isSharedCheck_4209_ = (!crate::leanh::lean_is_exclusive(v_x_4200_)) as u8;
                    if v_isSharedCheck_4209_ == 0 {
                        v___x_4203_ = v_x_4200_;
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4201_);
                        crate::leanh::lean_dec(v_x_4200_);
                        v___x_4203_ = crate::leanh::lean_box(0);
                        v_isShared_4204_ = v_isSharedCheck_4209_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4210_ = crate::leanh::lean_box(0);
                    v___x_4211_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4211_, 0, v_x_4200_);
                    crate::leanh::lean_ctor_set(v___x_4211_, 1, v___x_4210_);
                    v___x_4212_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4212_, 0, v_x_4199_);
                    crate::leanh::lean_ctor_set(v___x_4212_, 1, v___x_4211_);
                    v___x_4213_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4213_, 0, v___x_4212_);
                    return v___x_4213_;
                }
            }
            1 => {
                v___x_4205_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4205_, 0, v_x_4199_);
                crate::leanh::lean_ctor_set(v___x_4205_, 1, v_a_4201_);
                if v_isShared_4204_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4203_, 0, v___x_4205_);
                    v___x_4207_ = v___x_4203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4208_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4208_, 0, v___x_4205_);
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
    mut v_x_4214_: *mut crate::leanh::LeanObject,
    mut v_x_4215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4215_) == 4 {
                    v_a_4216_ = crate::leanh::lean_ctor_get(v_x_4215_, 0);
                    v_isSharedCheck_4224_ = (!crate::leanh::lean_is_exclusive(v_x_4215_)) as u8;
                    if v_isSharedCheck_4224_ == 0 {
                        v___x_4218_ = v_x_4215_;
                        v_isShared_4219_ = v_isSharedCheck_4224_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4216_);
                        crate::leanh::lean_dec(v_x_4215_);
                        v___x_4218_ = crate::leanh::lean_box(0);
                        v_isShared_4219_ = v_isSharedCheck_4224_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4225_ = crate::leanh::lean_box(0);
                    v___x_4226_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4226_, 0, v_x_4215_);
                    crate::leanh::lean_ctor_set(v___x_4226_, 1, v___x_4225_);
                    v___x_4227_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4227_, 0, v_x_4214_);
                    crate::leanh::lean_ctor_set(v___x_4227_, 1, v___x_4226_);
                    v___x_4228_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4228_, 0, v___x_4227_);
                    return v___x_4228_;
                }
            }
            1 => {
                v___x_4220_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4220_, 0, v_x_4214_);
                crate::leanh::lean_ctor_set(v___x_4220_, 1, v_a_4216_);
                if v_isShared_4219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4218_, 0, v___x_4220_);
                    v___x_4222_ = v___x_4218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4220_);
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
    mut v_l_4247_: *mut crate::leanh::LeanObject,
    mut v_a_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvars_4265_: u8 = 0;
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lIndex_x3f_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4273_: u8 = 0;
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_l_4247_) {
                0 => {
                    v___x_4249_ = l_Lean_Level_PP_toResult___closed__0;
                    return v___x_4249_;
                }
                1 => {
                    v_a_4250_ = crate::leanh::lean_ctor_get(v_l_4247_, 0);
                    crate::leanh::lean_inc(v_a_4250_);
                    crate::leanh::lean_dec_ref_known(v_l_4247_, 1);
                    v___x_4251_ = l_Lean_Level_PP_toResult(v_a_4250_, v_a_4248_);
                    v___x_4252_ = l_Lean_Level_PP_Result_succ(v___x_4251_);
                    return v___x_4252_;
                }
                2 => {
                    v_a_4253_ = crate::leanh::lean_ctor_get(v_l_4247_, 0);
                    crate::leanh::lean_inc(v_a_4253_);
                    v_a_4254_ = crate::leanh::lean_ctor_get(v_l_4247_, 1);
                    crate::leanh::lean_inc(v_a_4254_);
                    crate::leanh::lean_dec_ref_known(v_l_4247_, 2);
                    v___x_4255_ = l_Lean_Level_PP_toResult(v_a_4253_, v_a_4248_);
                    v___x_4256_ = l_Lean_Level_PP_toResult(v_a_4254_, v_a_4248_);
                    v___x_4257_ = l_Lean_Level_PP_Result_max(v___x_4255_, v___x_4256_);
                    return v___x_4257_;
                }
                3 => {
                    v_a_4258_ = crate::leanh::lean_ctor_get(v_l_4247_, 0);
                    crate::leanh::lean_inc(v_a_4258_);
                    v_a_4259_ = crate::leanh::lean_ctor_get(v_l_4247_, 1);
                    crate::leanh::lean_inc(v_a_4259_);
                    crate::leanh::lean_dec_ref_known(v_l_4247_, 2);
                    v___x_4260_ = l_Lean_Level_PP_toResult(v_a_4258_, v_a_4248_);
                    v___x_4261_ = l_Lean_Level_PP_toResult(v_a_4259_, v_a_4248_);
                    v___x_4262_ = l_Lean_Level_PP_Result_imax(v___x_4260_, v___x_4261_);
                    return v___x_4262_;
                }
                4 => {
                    v_a_4263_ = crate::leanh::lean_ctor_get(v_l_4247_, 0);
                    crate::leanh::lean_inc(v_a_4263_);
                    crate::leanh::lean_dec_ref_known(v_l_4247_, 1);
                    v___x_4264_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4264_, 0, v_a_4263_);
                    return v___x_4264_;
                }
                _ => {
                    v_mvars_4265_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4248_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_mvars_4265_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_l_4247_, 1);
                        v___x_4266_ = l_Lean_Level_PP_toResult___closed__3;
                        return v___x_4266_;
                    } else {
                        v_a_4267_ = crate::leanh::lean_ctor_get(v_l_4247_, 0);
                        crate::leanh::lean_inc_n(v_a_4267_, 2);
                        crate::leanh::lean_dec_ref_known(v_l_4247_, 1);
                        v_lIndex_x3f_4268_ = crate::leanh::lean_ctor_get(v_a_4248_, 0);
                        crate::leanh::lean_inc_ref(v_lIndex_x3f_4268_);
                        v___x_4269_ = crate::leanh::lean_apply_1(v_lIndex_x3f_4268_, v_a_4267_);
                        if crate::leanh::lean_obj_tag(v___x_4269_) == 1 {
                            crate::leanh::lean_dec(v_a_4267_);
                            v_val_4270_ = crate::leanh::lean_ctor_get(v___x_4269_, 0);
                            v_isSharedCheck_4281_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4269_)) as u8;
                            if v_isSharedCheck_4281_ == 0 {
                                v___x_4272_ = v___x_4269_;
                                v_isShared_4273_ = v_isSharedCheck_4281_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_4270_);
                                crate::leanh::lean_dec(v___x_4269_);
                                v___x_4272_ = crate::leanh::lean_box(0);
                                v_isShared_4273_ = v_isSharedCheck_4281_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4269_);
                            v___x_4282_ = l_Lean_Level_PP_toResult___closed__7;
                            v___x_4283_ = l_Lean_Level_PP_toResult___closed__9;
                            v___x_4284_ =
                                l_Lean_Name_replacePrefix(v_a_4267_, v___x_4282_, v___x_4283_);
                            v___x_4285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4285_, 0, v___x_4284_);
                            return v___x_4285_;
                        }
                    }
                }
            },
            1 => {
                v___x_4274_ = l_Lean_Level_PP_toResult___closed__5;
                v___x_4275_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4276_ = lean_nat_add(v_val_4270_, v___x_4275_);
                crate::leanh::lean_dec(v_val_4270_);
                v___x_4277_ = l_Lean_Name_num___override(v___x_4274_, v___x_4276_);
                if v_isShared_4273_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4272_, 0);
                    crate::leanh::lean_ctor_set(v___x_4272_, 0, v___x_4277_);
                    v___x_4279_ = v___x_4272_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v___x_4277_);
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
    mut v_l_4286_: *mut crate::leanh::LeanObject,
    mut v_a_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4288_ = l_Lean_Level_PP_toResult(v_l_4286_, v_a_4287_);
    crate::leanh::lean_dec_ref(v_a_4287_);
    return v_res_4288_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
    v___x_4291_ = lean_string_length(v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = crate::leanh::lean_obj_once(
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
    mut v_x_4298_: *mut crate::leanh::LeanObject,
    mut v_x_4299_: u8,
) -> *mut crate::leanh::LeanObject {
    if v_x_4299_ == 0 {
        let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4306_: u8 = 0;
        let mut v___x_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4300_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2
            ),
            core::ptr::addr_of_mut!(
                l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2_once
            ),
            _init_l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__2,
        );
        v___x_4301_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__3;
        v___x_4302_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4302_, 0, v___x_4301_);
        crate::leanh::lean_ctor_set(v___x_4302_, 1, v_x_4298_);
        v___x_4303_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__4;
        v___x_4304_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4304_, 0, v___x_4302_);
        crate::leanh::lean_ctor_set(v___x_4304_, 1, v___x_4303_);
        v___x_4305_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4305_, 0, v___x_4300_);
        crate::leanh::lean_ctor_set(v___x_4305_, 1, v___x_4304_);
        v___x_4306_ = 0;
        v___x_4307_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_4307_, 0, v___x_4305_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_4307_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_4306_,
        );
        return v___x_4307_;
    } else {
        return v_x_4298_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___boxed(
    mut v_x_4308_: *mut crate::leanh::LeanObject,
    mut v_x_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_57__boxed_4310_: u8 = 0;
    let mut v_res_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_57__boxed_4310_ = (crate::leanh::lean_unbox(v_x_4309_) as u8);
    v_res_4311_ =
        l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v_x_4308_, v_x_57__boxed_4310_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Level_PP_Result_format(
    mut v_x_4321_: *mut crate::leanh::LeanObject,
    mut v_x_4322_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4326_: u8 = 0;
    let mut v___x_4327_: u8 = 0;
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4332_: u8 = 0;
    let mut v_a_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_zero_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4348_: u8 = 0;
    let mut v_one_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_x27_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4362_: u8 = 0;
    let mut v_a_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: u8 = 0;
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_4321_) {
                0 => {
                    v_a_4323_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    v_isSharedCheck_4332_ = (!crate::leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4332_ == 0 {
                        v___x_4325_ = v_x_4321_;
                        v_isShared_4326_ = v_isSharedCheck_4332_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4323_);
                        crate::leanh::lean_dec(v_x_4321_);
                        v___x_4325_ = crate::leanh::lean_box(0);
                        v_isShared_4326_ = v_isSharedCheck_4332_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_4333_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    v_isSharedCheck_4341_ = (!crate::leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4341_ == 0 {
                        v___x_4335_ = v_x_4321_;
                        v_isShared_4336_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4333_);
                        crate::leanh::lean_dec(v_x_4321_);
                        v___x_4335_ = crate::leanh::lean_box(0);
                        v_isShared_4336_ = v_isSharedCheck_4341_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_4342_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    v_a_4343_ = crate::leanh::lean_ctor_get(v_x_4321_, 1);
                    v_isSharedCheck_4362_ = (!crate::leanh::lean_is_exclusive(v_x_4321_)) as u8;
                    if v_isSharedCheck_4362_ == 0 {
                        v___x_4345_ = v_x_4321_;
                        v_isShared_4346_ = v_isSharedCheck_4362_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4343_);
                        crate::leanh::lean_inc(v_a_4342_);
                        crate::leanh::lean_dec(v_x_4321_);
                        v___x_4345_ = crate::leanh::lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4362_;
                        state = 5;
                        continue;
                    }
                }
                3 => {
                    v_a_4363_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    crate::leanh::lean_inc(v_a_4363_);
                    crate::leanh::lean_dec_ref_known(v_x_4321_, 1);
                    v___x_4364_ = l_Lean_Level_PP_Result_format___closed__3;
                    v___x_4365_ =
                        l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_4363_);
                    v___x_4366_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4366_, 0, v___x_4364_);
                    crate::leanh::lean_ctor_set(v___x_4366_, 1, v___x_4365_);
                    v___x_4367_ = 0;
                    v___x_4368_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4368_, 0, v___x_4366_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4368_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v___x_4367_,
                    );
                    v___x_4369_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(
                        v___x_4368_,
                        v_x_4322_,
                    );
                    return v___x_4369_;
                }
                _ => {
                    v_a_4370_ = crate::leanh::lean_ctor_get(v_x_4321_, 0);
                    crate::leanh::lean_inc(v_a_4370_);
                    crate::leanh::lean_dec_ref_known(v_x_4321_, 1);
                    v___x_4371_ = l_Lean_Level_PP_Result_format___closed__5;
                    v___x_4372_ =
                        l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_a_4370_);
                    v___x_4373_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4373_, 0, v___x_4371_);
                    crate::leanh::lean_ctor_set(v___x_4373_, 1, v___x_4372_);
                    v___x_4374_ = 0;
                    v___x_4375_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4375_, 0, v___x_4373_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4375_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
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
                    crate::leanh::lean_ctor_set_tag(v___x_4325_, 3);
                    crate::leanh::lean_ctor_set(v___x_4325_, 0, v___x_4328_);
                    v___x_4330_ = v___x_4325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4331_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4331_, 0, v___x_4328_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_4335_, 3);
                    crate::leanh::lean_ctor_set(v___x_4335_, 0, v___x_4337_);
                    v___x_4339_ = v___x_4335_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4337_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4339_;
            }
            5 => {
                v_zero_4347_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4348_ = lean_nat_dec_eq(v_a_4343_, v_zero_4347_);
                if v_isZero_4348_ == 1 {
                    crate::leanh::lean_del_object(v___x_4345_);
                    crate::leanh::lean_dec(v_a_4343_);
                    v_x_4321_ = v_a_4342_;
                    state = 0;
                    continue;
                } else {
                    v_one_4350_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4351_ = lean_nat_sub(v_a_4343_, v_one_4350_);
                    crate::leanh::lean_dec(v_a_4343_);
                    v_f_x27_4352_ = l_Lean_Level_PP_Result_format(v_a_4342_, v_isZero_4348_);
                    v___x_4353_ = l_Lean_Level_PP_Result_format___closed__1;
                    if v_isShared_4346_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4345_, 5);
                        crate::leanh::lean_ctor_set(v___x_4345_, 1, v___x_4353_);
                        crate::leanh::lean_ctor_set(v___x_4345_, 0, v_f_x27_4352_);
                        v___x_4355_ = v___x_4345_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4361_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_f_x27_4352_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4361_, 1, v___x_4353_);
                        v___x_4355_ = v_reuseFailAlloc_4361_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4356_ = lean_nat_add(v_n_4351_, v_one_4350_);
                crate::leanh::lean_dec(v_n_4351_);
                v___x_4357_ = l_Nat_reprFast(v___x_4356_);
                v___x_4358_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4358_, 0, v___x_4357_);
                v___x_4359_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4359_, 0, v___x_4355_);
                crate::leanh::lean_ctor_set(v___x_4359_, 1, v___x_4358_);
                v___x_4360_ =
                    l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse(v___x_4359_, v_x_4322_);
                return v___x_4360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(
    mut v_x_4377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4383_: u8 = 0;
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4377_) == 0 {
                    v___x_4378_ = crate::leanh::lean_box(0);
                    return v___x_4378_;
                } else {
                    v_head_4379_ = crate::leanh::lean_ctor_get(v_x_4377_, 0);
                    v_tail_4380_ = crate::leanh::lean_ctor_get(v_x_4377_, 1);
                    v_isSharedCheck_4392_ = (!crate::leanh::lean_is_exclusive(v_x_4377_)) as u8;
                    if v_isSharedCheck_4392_ == 0 {
                        v___x_4382_ = v_x_4377_;
                        v_isShared_4383_ = v_isSharedCheck_4392_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4380_);
                        crate::leanh::lean_inc(v_head_4379_);
                        crate::leanh::lean_dec(v_x_4377_);
                        v___x_4382_ = crate::leanh::lean_box(0);
                        v_isShared_4383_ = v_isSharedCheck_4392_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4384_ = crate::leanh::lean_box(1);
                v___x_4385_ = 0;
                v___x_4386_ = l_Lean_Level_PP_Result_format(v_head_4379_, v___x_4385_);
                if v_isShared_4383_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4382_, 5);
                    crate::leanh::lean_ctor_set(v___x_4382_, 1, v___x_4386_);
                    crate::leanh::lean_ctor_set(v___x_4382_, 0, v___x_4384_);
                    v___x_4388_ = v___x_4382_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v___x_4384_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 1, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4389_ =
                    l___private_Lean_Level_0__Lean_Level_PP_Result_formatLst(v_tail_4380_);
                v___x_4390_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4390_, 0, v___x_4388_);
                crate::leanh::lean_ctor_set(v___x_4390_, 1, v___x_4389_);
                return v___x_4390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_PP_Result_format___boxed(
    mut v_x_4393_: *mut crate::leanh::LeanObject,
    mut v_x_4394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_270__boxed_4395_: u8 = 0;
    let mut v_res_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_270__boxed_4395_ = (crate::leanh::lean_unbox(v_x_4394_) as u8);
    v_res_4396_ = l_Lean_Level_PP_Result_format(v_x_4393_, v_x_270__boxed_4395_);
    return v_res_4396_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_4397_: u8 = 0;
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4397_ = 0;
    v___x_4398_ = crate::leanh::lean_box(0);
    v___x_4399_ = l_Lean_SourceInfo_fromRef(v___x_4398_, v___x_4397_);
    return v___x_4399_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4409_ = l___private_Lean_Level_0__Lean_Level_PP_parenIfFalse___closed__0;
    v___x_4410_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4411_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4411_, 0, v___x_4410_);
    crate::leanh::lean_ctor_set(v___x_4411_, 1, v___x_4409_);
    return v___x_4411_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4412_ = l_Lean_instReprData___lam__0___closed__0;
    v___x_4413_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4414_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4414_, 0, v___x_4413_);
    crate::leanh::lean_ctor_set(v___x_4414_, 1, v___x_4412_);
    return v___x_4414_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__12() -> *mut crate::leanh::LeanObject {
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4427_ = l_Lean_Level_PP_Result_format___closed__2;
    v___x_4428_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4429_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4429_, 0, v___x_4428_);
    crate::leanh::lean_ctor_set(v___x_4429_, 1, v___x_4427_);
    return v___x_4429_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__15() -> *mut crate::leanh::LeanObject {
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4433_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4433_;
}
pub unsafe fn _init_l_Lean_Level_PP_Result_quote___closed__17() -> *mut crate::leanh::LeanObject {
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4439_ = l_Lean_Level_PP_Result_format___closed__4;
    v___x_4440_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
        _init_l_Lean_Level_PP_Result_quote___closed__0,
    );
    v___x_4441_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4441_, 0, v___x_4440_);
    crate::leanh::lean_ctor_set(v___x_4441_, 1, v___x_4439_);
    return v___x_4441_;
}
pub unsafe fn l_Lean_Level_PP_Result_quote(
    mut v_r_4442_: *mut crate::leanh::LeanObject,
    mut v_prec_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v_zero_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4465_: u8 = 0;
    let mut v_one_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4483_: u8 = 0;
    let mut v_a_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4491_: usize = 0;
    let mut v___x_4492_: usize = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4504_: usize = 0;
    let mut v___x_4505_: usize = 0;
    let mut v___x_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_r_4442_) {
                0 => {
                    v_a_4453_ = crate::leanh::lean_ctor_get(v_r_4442_, 0);
                    crate::leanh::lean_inc(v_a_4453_);
                    crate::leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4454_ = lean_mk_syntax_ident(v_a_4453_);
                    return v___x_4454_;
                }
                1 => {
                    v_a_4455_ = crate::leanh::lean_ctor_get(v_r_4442_, 0);
                    crate::leanh::lean_inc(v_a_4455_);
                    crate::leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4456_ = l_Nat_reprFast(v_a_4455_);
                    v___x_4457_ = crate::leanh::lean_box(2);
                    v___x_4458_ = l_Lean_Syntax_mkNumLit(v___x_4456_, v___x_4457_);
                    return v___x_4458_;
                }
                2 => {
                    v_a_4459_ = crate::leanh::lean_ctor_get(v_r_4442_, 0);
                    v_a_4460_ = crate::leanh::lean_ctor_get(v_r_4442_, 1);
                    v_isSharedCheck_4483_ = (!crate::leanh::lean_is_exclusive(v_r_4442_)) as u8;
                    if v_isSharedCheck_4483_ == 0 {
                        v___x_4462_ = v_r_4442_;
                        v_isShared_4463_ = v_isSharedCheck_4483_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4460_);
                        crate::leanh::lean_inc(v_a_4459_);
                        crate::leanh::lean_dec(v_r_4442_);
                        v___x_4462_ = crate::leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4483_;
                        state = 2;
                        continue;
                    }
                }
                3 => {
                    v_a_4484_ = crate::leanh::lean_ctor_get(v_r_4442_, 0);
                    crate::leanh::lean_inc(v_a_4484_);
                    crate::leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4485_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4486_ = l_Lean_Level_PP_Result_quote___closed__11;
                    v___x_4487_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__12),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__12_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__12,
                    );
                    v___x_4488_ = l_Lean_Level_PP_Result_quote___closed__14;
                    v___x_4489_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__15,
                    );
                    v___x_4490_ = lean_array_mk(v_a_4484_);
                    v_sz_4491_ = lean_array_size(v___x_4490_);
                    v___x_4492_ = 0usize;
                    v___x_4493_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_4491_, v___x_4492_, v___x_4490_);
                    v___x_4494_ = l_Array_append___redArg(v___x_4489_, v___x_4493_);
                    crate::leanh::lean_dec_ref(v___x_4493_);
                    v___x_4495_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4495_, 0, v___x_4485_);
                    crate::leanh::lean_ctor_set(v___x_4495_, 1, v___x_4488_);
                    crate::leanh::lean_ctor_set(v___x_4495_, 2, v___x_4494_);
                    v___x_4496_ =
                        l_Lean_Syntax_node2(v___x_4485_, v___x_4486_, v___x_4487_, v___x_4495_);
                    v_s_4445_ = v___x_4496_;
                    state = 1;
                    continue;
                }
                _ => {
                    v_a_4497_ = crate::leanh::lean_ctor_get(v_r_4442_, 0);
                    crate::leanh::lean_inc(v_a_4497_);
                    crate::leanh::lean_dec_ref_known(v_r_4442_, 1);
                    v___x_4498_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4499_ = l_Lean_Level_PP_Result_quote___closed__16;
                    v___x_4500_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__17),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__17_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__17,
                    );
                    v___x_4501_ = l_Lean_Level_PP_Result_quote___closed__14;
                    v___x_4502_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__15_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__15,
                    );
                    v___x_4503_ = lean_array_mk(v_a_4497_);
                    v_sz_4504_ = lean_array_size(v___x_4503_);
                    v___x_4505_ = 0usize;
                    v___x_4506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_4504_, v___x_4505_, v___x_4503_);
                    v___x_4507_ = l_Array_append___redArg(v___x_4502_, v___x_4506_);
                    crate::leanh::lean_dec_ref(v___x_4506_);
                    v___x_4508_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4508_, 0, v___x_4498_);
                    crate::leanh::lean_ctor_set(v___x_4508_, 1, v___x_4501_);
                    crate::leanh::lean_ctor_set(v___x_4508_, 2, v___x_4507_);
                    v___x_4509_ =
                        l_Lean_Syntax_node2(v___x_4498_, v___x_4499_, v___x_4500_, v___x_4508_);
                    v_s_4445_ = v___x_4509_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_4446_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4447_ = lean_nat_dec_lt(v___x_4446_, v_prec_4443_);
                if v___x_4447_ == 0 {
                    return v_s_4445_;
                } else {
                    v___x_4448_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__0_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__0,
                    );
                    v___x_4449_ = l_Lean_Level_PP_Result_quote___closed__5;
                    v___x_4450_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Level_PP_Result_quote___closed__6_once),
                        _init_l_Lean_Level_PP_Result_quote___closed__6,
                    );
                    v___x_4451_ = crate::leanh::lean_obj_once(
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
                v_zero_4464_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4465_ = lean_nat_dec_eq(v_a_4460_, v_zero_4464_);
                if v_isZero_4465_ == 1 {
                    crate::leanh::lean_del_object(v___x_4462_);
                    crate::leanh::lean_dec(v_a_4460_);
                    v_r_4442_ = v_a_4459_;
                    state = 0;
                    continue;
                } else {
                    v_one_4467_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4468_ = lean_nat_sub(v_a_4460_, v_one_4467_);
                    crate::leanh::lean_dec(v_a_4460_);
                    v___x_4469_ = crate::leanh::lean_box(0);
                    v___x_4470_ = l_Lean_SourceInfo_fromRef(v___x_4469_, v_isZero_4465_);
                    v___x_4471_ = l_Lean_Level_PP_Result_quote___closed__9;
                    v___x_4472_ = crate::leanh::lean_unsigned_to_nat(65);
                    v___x_4473_ = l_Lean_Level_PP_Result_quote(v_a_4459_, v___x_4472_);
                    v___x_4474_ = l_Lean_Level_PP_Result_quote___closed__10;
                    crate::leanh::lean_inc(v___x_4470_);
                    if v_isShared_4463_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4462_, 1, v___x_4474_);
                        crate::leanh::lean_ctor_set(v___x_4462_, 0, v___x_4470_);
                        v___x_4476_ = v___x_4462_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4482_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 0, v___x_4470_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4482_, 1, v___x_4474_);
                        v___x_4476_ = v_reuseFailAlloc_4482_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4477_ = lean_nat_add(v_n_4468_, v_one_4467_);
                crate::leanh::lean_dec(v_n_4468_);
                v___x_4478_ = l_Nat_reprFast(v___x_4477_);
                v___x_4479_ = crate::leanh::lean_box(2);
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
    mut v_bs_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4513_: u8 = 0;
    let mut v_v_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: usize = 0;
    let mut v___x_4520_: usize = 0;
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4513_ = lean_usize_dec_lt(v_i_4511_, v_sz_4510_);
                if v___x_4513_ == 0 {
                    return v_bs_4512_;
                } else {
                    v_v_4514_ = lean_array_uget(v_bs_4512_, v_i_4511_);
                    v___x_4515_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4516_ = lean_array_uset(v_bs_4512_, v_i_4511_, v___x_4515_);
                    v___x_4517_ = crate::leanh::lean_unsigned_to_nat(1024);
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
    mut v_sz_4523_: *mut crate::leanh::LeanObject,
    mut v_i_4524_: *mut crate::leanh::LeanObject,
    mut v_bs_4525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4526_: usize = 0;
    let mut v_i_boxed_4527_: usize = 0;
    let mut v_res_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4526_ = crate::leanh::lean_unbox_usize(v_sz_4523_);
    crate::leanh::lean_dec(v_sz_4523_);
    v_i_boxed_4527_ = crate::leanh::lean_unbox_usize(v_i_4524_);
    crate::leanh::lean_dec(v_i_4524_);
    v_res_4528_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Level_PP_Result_quote_spec__0(v_sz_boxed_4526_, v_i_boxed_4527_, v_bs_4525_);
    return v_res_4528_;
}
pub unsafe fn l_Lean_Level_PP_Result_quote___boxed(
    mut v_r_4529_: *mut crate::leanh::LeanObject,
    mut v_prec_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4531_ = l_Lean_Level_PP_Result_quote(v_r_4529_, v_prec_4530_);
    crate::leanh::lean_dec(v_prec_4530_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_Level_format(
    mut v_u_4532_: *mut crate::leanh::LeanObject,
    mut v_mvars_4533_: u8,
    mut v_lIndex_x3f_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: u8 = 0;
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4535_, 0, v_lIndex_x3f_4534_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4535_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_mvars_4533_,
    );
    v___x_4536_ = l_Lean_Level_PP_toResult(v_u_4532_, v___x_4535_);
    crate::leanh::lean_dec_ref_known(v___x_4535_, 1);
    v___x_4537_ = 1;
    v___x_4538_ = l_Lean_Level_PP_Result_format(v___x_4536_, v___x_4537_);
    return v___x_4538_;
}
pub unsafe fn l_Lean_Level_format___boxed(
    mut v_u_4539_: *mut crate::leanh::LeanObject,
    mut v_mvars_4540_: *mut crate::leanh::LeanObject,
    mut v_lIndex_x3f_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvars_boxed_4542_: u8 = 0;
    let mut v_res_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mvars_boxed_4542_ = (crate::leanh::lean_unbox(v_mvars_4540_) as u8);
    v_res_4543_ = l_Lean_Level_format(v_u_4539_, v_mvars_boxed_4542_, v_lIndex_x3f_4541_);
    return v_res_4543_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__0(
    mut v_x_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4545_ = crate::leanh::lean_box(0);
    return v___x_4545_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__0___boxed(
    mut v_x_4546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4547_ = l_Lean_Level_instToFormat___lam__0(v_x_4546_);
    crate::leanh::lean_dec(v_x_4546_);
    return v_res_4547_;
}
pub unsafe fn l_Lean_Level_instToFormat___lam__1(
    mut v___f_4548_: *mut crate::leanh::LeanObject,
    mut v_u_4549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4550_ = 1;
    v___x_4551_ = l_Lean_Level_format(v_u_4549_, v___x_4550_, v___f_4548_);
    return v___x_4551_;
}
pub unsafe fn l_Lean_Level_instToString___lam__1(
    mut v___f_4556_: *mut crate::leanh::LeanObject,
    mut v_u_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: u8 = 0;
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = 1;
    v___x_4559_ = l_Lean_Level_format(v_u_4557_, v___x_4558_, v___f_4556_);
    v___x_4560_ = l_Std_Format_defWidth;
    v___x_4561_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4562_ = l_Std_Format_pretty(v___x_4559_, v___x_4560_, v___x_4561_, v___x_4561_);
    return v___x_4562_;
}
pub unsafe fn l_Lean_Level_quote(
    mut v_u_4566_: *mut crate::leanh::LeanObject,
    mut v_prec_4567_: *mut crate::leanh::LeanObject,
    mut v_mvars_4568_: u8,
    mut v_lIndex_x3f_4569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4570_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_4570_, 0, v_lIndex_x3f_4569_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4570_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v_mvars_4568_,
    );
    v___x_4571_ = l_Lean_Level_PP_toResult(v_u_4566_, v___x_4570_);
    crate::leanh::lean_dec_ref_known(v___x_4570_, 1);
    v___x_4572_ = l_Lean_Level_PP_Result_quote(v___x_4571_, v_prec_4567_);
    return v___x_4572_;
}
pub unsafe fn l_Lean_Level_quote___boxed(
    mut v_u_4573_: *mut crate::leanh::LeanObject,
    mut v_prec_4574_: *mut crate::leanh::LeanObject,
    mut v_mvars_4575_: *mut crate::leanh::LeanObject,
    mut v_lIndex_x3f_4576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mvars_boxed_4577_: u8 = 0;
    let mut v_res_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_mvars_boxed_4577_ = (crate::leanh::lean_unbox(v_mvars_4575_) as u8);
    v_res_4578_ = l_Lean_Level_quote(
        v_u_4573_,
        v_prec_4574_,
        v_mvars_boxed_4577_,
        v_lIndex_x3f_4576_,
    );
    crate::leanh::lean_dec(v_prec_4574_);
    return v_res_4578_;
}
pub unsafe fn l_Lean_Level_instQuoteMkStr1___lam__1(
    mut v___f_4579_: *mut crate::leanh::LeanObject,
    mut v_u_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: u8 = 0;
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4581_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4582_ = 1;
    v___x_4583_ = l_Lean_Level_quote(v_u_4580_, v___x_4581_, v___x_4582_, v___f_4579_);
    return v___x_4583_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(
    mut v_u_4587_: *mut crate::leanh::LeanObject,
    mut v_v_4588_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4590_: u8 = 0;
    let mut v___x_4591_: u8 = 0;
    let mut v_a_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: u8 = 0;
    let mut v___x_4595_: u8 = 0;
    let mut v___x_4596_: u8 = 0;
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_dec(v___x_4598_);
                    crate::leanh::lean_dec(v___x_4597_);
                    v___y_4590_ = v___x_4599_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4591_ = 1;
                if v___y_4590_ == 0 {
                    if crate::leanh::lean_obj_tag(v_u_4587_) == 2 {
                        v_a_4592_ = crate::leanh::lean_ctor_get(v_u_4587_, 0);
                        v_a_4593_ = crate::leanh::lean_ctor_get(v_u_4587_, 1);
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
    mut v_u_4600_: *mut crate::leanh::LeanObject,
    mut v_v_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4602_: u8 = 0;
    let mut v_r_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4602_ = l___private_Lean_Level_0__Lean_mkLevelMaxCore___lam__0(v_u_4600_, v_v_4601_);
    crate::leanh::lean_dec(v_v_4601_);
    crate::leanh::lean_dec(v_u_4600_);
    v_r_4603_ = crate::leanh::lean_box((v_res_4602_) as usize);
    return v_r_4603_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore(
    mut v_u_4604_: *mut crate::leanh::LeanObject,
    mut v_v_4605_: *mut crate::leanh::LeanObject,
    mut v_elseK_4606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                        let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4614_: u8 = 0;
                        v___x_4612_ = l_Lean_Level_getLevelOffset(v_u_4604_);
                        v___x_4613_ = l_Lean_Level_getLevelOffset(v_v_4605_);
                        v___x_4614_ = lean_level_eq(v___x_4612_, v___x_4613_);
                        crate::leanh::lean_dec(v___x_4613_);
                        crate::leanh::lean_dec(v___x_4612_);
                        if v___x_4614_ == 0 {
                            let mut v___x_4615_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4616_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_4615_ = crate::leanh::lean_box(0);
                            v___x_4616_ = crate::leanh::lean_apply_1(v_elseK_4606_, v___x_4615_);
                            return v___x_4616_;
                        } else {
                            let mut v___x_4617_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4618_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4619_: u8 = 0;
                            crate::leanh::lean_dec_ref(v_elseK_4606_);
                            v___x_4617_ = l_Lean_Level_getOffset(v_v_4605_);
                            v___x_4618_ = l_Lean_Level_getOffset(v_u_4604_);
                            v___x_4619_ = lean_nat_dec_le(v___x_4617_, v___x_4618_);
                            crate::leanh::lean_dec(v___x_4618_);
                            crate::leanh::lean_dec(v___x_4617_);
                            if v___x_4619_ == 0 {
                                crate::leanh::lean_inc(v_v_4605_);
                                return v_v_4605_;
                            } else {
                                crate::leanh::lean_inc(v_u_4604_);
                                return v_u_4604_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_elseK_4606_);
                        crate::leanh::lean_inc(v_v_4605_);
                        return v_v_4605_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_elseK_4606_);
                    crate::leanh::lean_inc(v_u_4604_);
                    return v_u_4604_;
                }
            } else {
                crate::leanh::lean_dec_ref(v_elseK_4606_);
                crate::leanh::lean_inc(v_u_4604_);
                return v_u_4604_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_elseK_4606_);
            crate::leanh::lean_inc(v_v_4605_);
            return v_v_4605_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_elseK_4606_);
        crate::leanh::lean_inc(v_u_4604_);
        return v_u_4604_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelMaxCore___boxed(
    mut v_u_4620_: *mut crate::leanh::LeanObject,
    mut v_v_4621_: *mut crate::leanh::LeanObject,
    mut v_elseK_4622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4623_ =
        l___private_Lean_Level_0__Lean_mkLevelMaxCore(v_u_4620_, v_v_4621_, v_elseK_4622_);
    crate::leanh::lean_dec(v_v_4621_);
    crate::leanh::lean_dec(v_u_4620_);
    return v_res_4623_;
}
pub unsafe fn l_Lean_mkLevelMax_x27(
    mut v_u_4624_: *mut crate::leanh::LeanObject,
    mut v_v_4625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                        let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4633_: u8 = 0;
                        v___x_4631_ = l_Lean_Level_getLevelOffset(v_u_4624_);
                        v___x_4632_ = l_Lean_Level_getLevelOffset(v_v_4625_);
                        v___x_4633_ = lean_level_eq(v___x_4631_, v___x_4632_);
                        crate::leanh::lean_dec(v___x_4632_);
                        crate::leanh::lean_dec(v___x_4631_);
                        if v___x_4633_ == 0 {
                            let mut v___x_4634_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_4634_ = l_Lean_Level_max___override(v_u_4624_, v_v_4625_);
                            return v___x_4634_;
                        } else {
                            let mut v___x_4635_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4636_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4637_: u8 = 0;
                            v___x_4635_ = l_Lean_Level_getOffset(v_v_4625_);
                            v___x_4636_ = l_Lean_Level_getOffset(v_u_4624_);
                            v___x_4637_ = lean_nat_dec_le(v___x_4635_, v___x_4636_);
                            crate::leanh::lean_dec(v___x_4636_);
                            crate::leanh::lean_dec(v___x_4635_);
                            if v___x_4637_ == 0 {
                                crate::leanh::lean_dec(v_u_4624_);
                                return v_v_4625_;
                            } else {
                                crate::leanh::lean_dec(v_v_4625_);
                                return v_u_4624_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_u_4624_);
                        return v_v_4625_;
                    }
                } else {
                    crate::leanh::lean_dec(v_v_4625_);
                    return v_u_4624_;
                }
            } else {
                crate::leanh::lean_dec(v_v_4625_);
                return v_u_4624_;
            }
        } else {
            crate::leanh::lean_dec(v_u_4624_);
            return v_v_4625_;
        }
    } else {
        crate::leanh::lean_dec(v_v_4625_);
        return v_u_4624_;
    }
}
pub unsafe fn l_Lean_simpLevelMax_x27(
    mut v_u_4638_: *mut crate::leanh::LeanObject,
    mut v_v_4639_: *mut crate::leanh::LeanObject,
    mut v_d_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                        let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4648_: u8 = 0;
                        v___x_4646_ = l_Lean_Level_getLevelOffset(v_u_4638_);
                        v___x_4647_ = l_Lean_Level_getLevelOffset(v_v_4639_);
                        v___x_4648_ = lean_level_eq(v___x_4646_, v___x_4647_);
                        crate::leanh::lean_dec(v___x_4647_);
                        crate::leanh::lean_dec(v___x_4646_);
                        if v___x_4648_ == 0 {
                            crate::leanh::lean_inc(v_d_4640_);
                            return v_d_4640_;
                        } else {
                            let mut v___x_4649_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4650_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4651_: u8 = 0;
                            v___x_4649_ = l_Lean_Level_getOffset(v_v_4639_);
                            v___x_4650_ = l_Lean_Level_getOffset(v_u_4638_);
                            v___x_4651_ = lean_nat_dec_le(v___x_4649_, v___x_4650_);
                            crate::leanh::lean_dec(v___x_4650_);
                            crate::leanh::lean_dec(v___x_4649_);
                            if v___x_4651_ == 0 {
                                crate::leanh::lean_inc(v_v_4639_);
                                return v_v_4639_;
                            } else {
                                crate::leanh::lean_inc(v_u_4638_);
                                return v_u_4638_;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc(v_v_4639_);
                        return v_v_4639_;
                    }
                } else {
                    crate::leanh::lean_inc(v_u_4638_);
                    return v_u_4638_;
                }
            } else {
                crate::leanh::lean_inc(v_u_4638_);
                return v_u_4638_;
            }
        } else {
            crate::leanh::lean_inc(v_v_4639_);
            return v_v_4639_;
        }
    } else {
        crate::leanh::lean_inc(v_u_4638_);
        return v_u_4638_;
    }
}
pub unsafe fn l_Lean_simpLevelMax_x27___boxed(
    mut v_u_4652_: *mut crate::leanh::LeanObject,
    mut v_v_4653_: *mut crate::leanh::LeanObject,
    mut v_d_4654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_simpLevelMax_x27(v_u_4652_, v_v_4653_, v_d_4654_);
    crate::leanh::lean_dec(v_d_4654_);
    crate::leanh::lean_dec(v_v_4653_);
    crate::leanh::lean_dec(v_u_4652_);
    return v_res_4655_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_mkLevelIMaxCore(
    mut v_u_4656_: *mut crate::leanh::LeanObject,
    mut v_v_4657_: *mut crate::leanh::LeanObject,
    mut v_elseK_4658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                crate::leanh::lean_dec(v_v_4657_);
                if v___x_4662_ == 0 {
                    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_u_4656_);
                    v___x_4663_ = crate::leanh::lean_box(0);
                    v___x_4664_ = crate::leanh::lean_apply_1(v_elseK_4658_, v___x_4663_);
                    return v___x_4664_;
                } else {
                    crate::leanh::lean_dec_ref(v_elseK_4658_);
                    return v_u_4656_;
                }
            } else {
                crate::leanh::lean_dec_ref(v_elseK_4658_);
                crate::leanh::lean_dec(v_u_4656_);
                return v_v_4657_;
            }
        } else {
            crate::leanh::lean_dec_ref(v_elseK_4658_);
            crate::leanh::lean_dec(v_u_4656_);
            return v_v_4657_;
        }
    } else {
        let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_elseK_4658_);
        v___x_4665_ = l_Lean_mkLevelMax_x27(v_u_4656_, v_v_4657_);
        return v___x_4665_;
    }
}
pub unsafe fn l_Lean_mkLevelIMax_x27(
    mut v_u_4666_: *mut crate::leanh::LeanObject,
    mut v_v_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_4672_ = l_Lean_Level_imax___override(v_u_4666_, v_v_4667_);
                    return v___x_4672_;
                } else {
                    crate::leanh::lean_dec(v_v_4667_);
                    return v_u_4666_;
                }
            } else {
                crate::leanh::lean_dec(v_u_4666_);
                return v_v_4667_;
            }
        } else {
            crate::leanh::lean_dec(v_u_4666_);
            return v_v_4667_;
        }
    } else {
        let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4673_ = l_Lean_mkLevelMax_x27(v_u_4666_, v_v_4667_);
        return v___x_4673_;
    }
}
pub unsafe fn l_Lean_simpLevelIMax_x27(
    mut v_u_4674_: *mut crate::leanh::LeanObject,
    mut v_v_4675_: *mut crate::leanh::LeanObject,
    mut v_d_4676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
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
                crate::leanh::lean_dec(v_v_4675_);
                if v___x_4680_ == 0 {
                    crate::leanh::lean_dec(v_u_4674_);
                    crate::leanh::lean_inc(v_d_4676_);
                    return v_d_4676_;
                } else {
                    return v_u_4674_;
                }
            } else {
                crate::leanh::lean_dec(v_u_4674_);
                return v_v_4675_;
            }
        } else {
            crate::leanh::lean_dec(v_u_4674_);
            return v_v_4675_;
        }
    } else {
        let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4681_ = l_Lean_mkLevelMax_x27(v_u_4674_, v_v_4675_);
        return v___x_4681_;
    }
}
pub unsafe fn l_Lean_simpLevelIMax_x27___boxed(
    mut v_u_4682_: *mut crate::leanh::LeanObject,
    mut v_v_4683_: *mut crate::leanh::LeanObject,
    mut v_d_4684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4685_ = l_Lean_simpLevelIMax_x27(v_u_4682_, v_v_4683_, v_d_4684_);
    crate::leanh::lean_dec(v_d_4684_);
    return v_res_4685_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4688_ = l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl___closed__1;
    v___x_4689_ = crate::leanh::lean_unsigned_to_nat(14);
    v___x_4690_ = crate::leanh::lean_unsigned_to_nat(564);
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
    mut v_lvl_4694_: *mut crate::leanh::LeanObject,
    mut v_newLvl_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_lvl_4694_) == 1 {
        let mut v_a_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4697_: usize = 0;
        let mut v___x_4698_: usize = 0;
        let mut v___x_4699_: u8 = 0;
        v_a_4696_ = crate::leanh::lean_ctor_get(v_lvl_4694_, 0);
        v___x_4697_ = lean_ptr_addr(v_a_4696_);
        v___x_4698_ = lean_ptr_addr(v_newLvl_4695_);
        v___x_4699_ = lean_usize_dec_eq(v___x_4697_, v___x_4698_);
        if v___x_4699_ == 0 {
            let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4700_ = l_Lean_Level_succ___override(v_newLvl_4695_);
            return v___x_4700_;
        } else {
            crate::leanh::lean_dec(v_newLvl_4695_);
            crate::leanh::lean_inc_ref(v_lvl_4694_);
            return v_lvl_4694_;
        }
    } else {
        let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_newLvl_4695_);
        v___x_4701_ = crate::leanh::lean_box(0);
        v___x_4702_ = crate::leanh::lean_obj_once(
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
    mut v_lvl_4704_: *mut crate::leanh::LeanObject,
    mut v_newLvl_4705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4706_ =
        l___private_Lean_Level_0__Lean_Level_updateSucc_x21Impl(v_lvl_4704_, v_newLvl_4705_);
    crate::leanh::lean_dec(v_lvl_4704_);
    return v_res_4706_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___closed__1;
    v___x_4710_ = crate::leanh::lean_unsigned_to_nat(19);
    v___x_4711_ = crate::leanh::lean_unsigned_to_nat(575);
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
    mut v_lvl_4715_: *mut crate::leanh::LeanObject,
    mut v_newLhs_4716_: *mut crate::leanh::LeanObject,
    mut v_newRhs_4717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4719_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: usize = 0;
    let mut v___x_4725_: usize = 0;
    let mut v___x_4726_: u8 = 0;
    let mut v___x_4727_: usize = 0;
    let mut v___x_4728_: usize = 0;
    let mut v___x_4729_: u8 = 0;
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_lvl_4715_) == 2 {
                    v_a_4722_ = crate::leanh::lean_ctor_get(v_lvl_4715_, 0);
                    v_a_4723_ = crate::leanh::lean_ctor_get(v_lvl_4715_, 1);
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
                    crate::leanh::lean_dec(v_newRhs_4717_);
                    crate::leanh::lean_dec(v_newLhs_4716_);
                    v___x_4730_ = crate::leanh::lean_box(0);
                    v___x_4731_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_newRhs_4717_);
                    crate::leanh::lean_dec(v_newLhs_4716_);
                    return v___x_4721_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl___boxed(
    mut v_lvl_4733_: *mut crate::leanh::LeanObject,
    mut v_newLhs_4734_: *mut crate::leanh::LeanObject,
    mut v_newRhs_4735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4736_ = l___private_Lean_Level_0__Lean_Level_updateMax_x21Impl(
        v_lvl_4733_,
        v_newLhs_4734_,
        v_newRhs_4735_,
    );
    crate::leanh::lean_dec(v_lvl_4733_);
    return v_res_4736_;
}
pub unsafe fn _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__1;
    v___x_4740_ = crate::leanh::lean_unsigned_to_nat(20);
    v___x_4741_ = crate::leanh::lean_unsigned_to_nat(586);
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
    mut v_lvl_4745_: *mut crate::leanh::LeanObject,
    mut v_newLhs_4746_: *mut crate::leanh::LeanObject,
    mut v_newRhs_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4749_: u8 = 0;
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: usize = 0;
    let mut v___x_4755_: usize = 0;
    let mut v___x_4756_: u8 = 0;
    let mut v___x_4757_: usize = 0;
    let mut v___x_4758_: usize = 0;
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_lvl_4745_) == 3 {
                    v_a_4752_ = crate::leanh::lean_ctor_get(v_lvl_4745_, 0);
                    v_a_4753_ = crate::leanh::lean_ctor_get(v_lvl_4745_, 1);
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
                    crate::leanh::lean_dec(v_newRhs_4747_);
                    crate::leanh::lean_dec(v_newLhs_4746_);
                    v___x_4760_ = crate::leanh::lean_box(0);
                    v___x_4761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2_once), _init_l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl___closed__2);
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
    mut v_lvl_4763_: *mut crate::leanh::LeanObject,
    mut v_newLhs_4764_: *mut crate::leanh::LeanObject,
    mut v_newRhs_4765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4766_ = l___private_Lean_Level_0__Lean_Level_updateIMax_x21Impl(
        v_lvl_4763_,
        v_newLhs_4764_,
        v_newRhs_4765_,
    );
    crate::leanh::lean_dec(v_lvl_4763_);
    return v_res_4766_;
}
pub unsafe fn l_Lean_Level_mkNaryMax(
    mut v_x_4767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4767_) == 0 {
        let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4768_ = crate::leanh::lean_box(0);
        return v___x_4768_;
    } else {
        let mut v_tail_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_4769_ = crate::leanh::lean_ctor_get(v_x_4767_, 1);
        if crate::leanh::lean_obj_tag(v_tail_4769_) == 0 {
            let mut v_head_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_4770_ = crate::leanh::lean_ctor_get(v_x_4767_, 0);
            crate::leanh::lean_inc(v_head_4770_);
            crate::leanh::lean_dec_ref_known(v_x_4767_, 2);
            return v_head_4770_;
        } else {
            let mut v_head_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_4769_);
            v_head_4771_ = crate::leanh::lean_ctor_get(v_x_4767_, 0);
            crate::leanh::lean_inc(v_head_4771_);
            crate::leanh::lean_dec_ref_known(v_x_4767_, 2);
            v___x_4772_ = l_Lean_Level_mkNaryMax(v_tail_4769_);
            v___x_4773_ = l_Lean_mkLevelMax_x27(v_head_4771_, v___x_4772_);
            return v___x_4773_;
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_substParams_go(
    mut v_s_4774_: *mut crate::leanh::LeanObject,
    mut v_u_4775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: u8 = 0;
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: usize = 0;
    let mut v___x_4780_: usize = 0;
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: u8 = 0;
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4789_: u8 = 0;
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: usize = 0;
    let mut v___x_4793_: usize = 0;
    let mut v___x_4794_: u8 = 0;
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: u8 = 0;
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: u8 = 0;
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4804_: u8 = 0;
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: usize = 0;
    let mut v___x_4808_: usize = 0;
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: usize = 0;
    let mut v___x_4811_: usize = 0;
    let mut v___x_4812_: u8 = 0;
    let mut v_a_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_u_4775_) {
                0 => {
                    crate::leanh::lean_dec_ref(v_s_4774_);
                    return v_u_4775_;
                }
                1 => {
                    v_a_4776_ = crate::leanh::lean_ctor_get(v_u_4775_, 0);
                    v___x_4777_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4777_ == 0 {
                        crate::leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        crate::leanh::lean_inc(v_a_4776_);
                        v___x_4778_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4776_,
                        );
                        v___x_4779_ = lean_ptr_addr(v_a_4776_);
                        v___x_4780_ = lean_ptr_addr(v___x_4778_);
                        v___x_4781_ = lean_usize_dec_eq(v___x_4779_, v___x_4780_);
                        if v___x_4781_ == 0 {
                            crate::leanh::lean_dec_ref_known(v_u_4775_, 1);
                            v___x_4782_ = l_Lean_Level_succ___override(v___x_4778_);
                            return v___x_4782_;
                        } else {
                            crate::leanh::lean_dec(v___x_4778_);
                            return v_u_4775_;
                        }
                    }
                }
                2 => {
                    v_a_4783_ = crate::leanh::lean_ctor_get(v_u_4775_, 0);
                    v_a_4784_ = crate::leanh::lean_ctor_get(v_u_4775_, 1);
                    v___x_4785_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4785_ == 0 {
                        crate::leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        crate::leanh::lean_inc(v_a_4783_);
                        crate::leanh::lean_inc_ref(v_s_4774_);
                        v___x_4786_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4783_,
                        );
                        crate::leanh::lean_inc(v_a_4784_);
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
                    v_a_4798_ = crate::leanh::lean_ctor_get(v_u_4775_, 0);
                    v_a_4799_ = crate::leanh::lean_ctor_get(v_u_4775_, 1);
                    v___x_4800_ = l_Lean_Level_hasParam(v_u_4775_);
                    if v___x_4800_ == 0 {
                        crate::leanh::lean_dec_ref(v_s_4774_);
                        return v_u_4775_;
                    } else {
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_inc_ref(v_s_4774_);
                        v___x_4801_ = l___private_Lean_Level_0__Lean_Level_substParams_go(
                            v_s_4774_, v_a_4798_,
                        );
                        crate::leanh::lean_inc(v_a_4799_);
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
                    v_a_4813_ = crate::leanh::lean_ctor_get(v_u_4775_, 0);
                    crate::leanh::lean_inc(v_a_4813_);
                    v___x_4814_ = crate::leanh::lean_apply_1(v_s_4774_, v_a_4813_);
                    if crate::leanh::lean_obj_tag(v___x_4814_) == 0 {
                        return v_u_4775_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v_u_4775_, 1);
                        v_val_4815_ = crate::leanh::lean_ctor_get(v___x_4814_, 0);
                        crate::leanh::lean_inc(v_val_4815_);
                        crate::leanh::lean_dec_ref_known(v___x_4814_, 1);
                        return v_val_4815_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v_s_4774_);
                    return v_u_4775_;
                }
            },
            1 => {
                if v___y_4789_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_u_4775_, 2);
                    v___x_4790_ = l_Lean_mkLevelMax_x27(v___x_4786_, v___x_4787_);
                    return v___x_4790_;
                } else {
                    v___x_4791_ = l_Lean_simpLevelMax_x27(v___x_4786_, v___x_4787_, v_u_4775_);
                    crate::leanh::lean_dec_ref_known(v_u_4775_, 2);
                    crate::leanh::lean_dec(v___x_4787_);
                    crate::leanh::lean_dec(v___x_4786_);
                    return v___x_4791_;
                }
            }
            2 => {
                if v___y_4804_ == 0 {
                    crate::leanh::lean_dec_ref_known(v_u_4775_, 2);
                    v___x_4805_ = l_Lean_mkLevelIMax_x27(v___x_4801_, v___x_4802_);
                    return v___x_4805_;
                } else {
                    v___x_4806_ = l_Lean_simpLevelIMax_x27(v___x_4801_, v___x_4802_, v_u_4775_);
                    crate::leanh::lean_dec_ref_known(v_u_4775_, 2);
                    return v___x_4806_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_substParams(
    mut v_u_4816_: *mut crate::leanh::LeanObject,
    mut v_s_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v_s_4817_, v_u_4816_);
    return v___x_4818_;
}
pub unsafe fn l_Lean_Level_getParamSubst(
    mut v_x_4819_: *mut crate::leanh::LeanObject,
    mut v_x_4820_: *mut crate::leanh::LeanObject,
    mut v_x_4821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: u8 = 0;
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4819_) == 1 {
                    if crate::leanh::lean_obj_tag(v_x_4820_) == 1 {
                        v_head_4822_ = crate::leanh::lean_ctor_get(v_x_4819_, 0);
                        v_tail_4823_ = crate::leanh::lean_ctor_get(v_x_4819_, 1);
                        v_head_4824_ = crate::leanh::lean_ctor_get(v_x_4820_, 0);
                        v_tail_4825_ = crate::leanh::lean_ctor_get(v_x_4820_, 1);
                        v___x_4826_ = lean_name_eq(v_head_4822_, v_x_4821_);
                        if v___x_4826_ == 0 {
                            v_x_4819_ = v_tail_4823_;
                            v_x_4820_ = v_tail_4825_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_head_4824_);
                            v___x_4828_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4828_, 0, v_head_4824_);
                            return v___x_4828_;
                        }
                    } else {
                        v___x_4829_ = crate::leanh::lean_box(0);
                        return v___x_4829_;
                    }
                } else {
                    v___x_4830_ = crate::leanh::lean_box(0);
                    return v___x_4830_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_getParamSubst___boxed(
    mut v_x_4831_: *mut crate::leanh::LeanObject,
    mut v_x_4832_: *mut crate::leanh::LeanObject,
    mut v_x_4833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4834_ = l_Lean_Level_getParamSubst(v_x_4831_, v_x_4832_, v_x_4833_);
    crate::leanh::lean_dec(v_x_4833_);
    crate::leanh::lean_dec(v_x_4832_);
    crate::leanh::lean_dec(v_x_4831_);
    return v_res_4834_;
}
pub unsafe fn l_Lean_Level_instantiateParams(
    mut v_u_4835_: *mut crate::leanh::LeanObject,
    mut v_paramNames_4836_: *mut crate::leanh::LeanObject,
    mut v_vs_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4838_ = crate::leanh::lean_alloc_closure(
        l_Lean_Level_getParamSubst___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_4838_, 0, v_paramNames_4836_);
    crate::leanh::lean_closure_set(v___x_4838_, 1, v_vs_4837_);
    v___x_4839_ = l___private_Lean_Level_0__Lean_Level_substParams_go(v___x_4838_, v_u_4835_);
    return v___x_4839_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go(
    mut v_u_4840_: *mut crate::leanh::LeanObject,
    mut v_v_4841_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_4843_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: u8 = 0;
    let mut v_a_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: u8 = 0;
    let mut v_v_x27_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: u8 = 0;
    let mut v___x_4855_: u8 = 0;
    let mut v___y_4857_: u8 = 0;
    let mut v_u_u2081_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_u2082_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: u8 = 0;
    let mut v___x_4863_: u8 = 0;
    let mut v___x_4864_: u8 = 0;
    let mut v___x_4865_: u8 = 0;
    let mut v_a_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: u8 = 0;
    let mut v_a_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4864_ = lean_level_eq(v_u_4840_, v_v_4841_);
                if v___x_4864_ == 0 {
                    match crate::leanh::lean_obj_tag(v_v_4841_) {
                        0 => {
                            v___x_4865_ = 1;
                            return v___x_4865_;
                        }
                        2 => {
                            v_a_4866_ = crate::leanh::lean_ctor_get(v_v_4841_, 0);
                            v_a_4867_ = crate::leanh::lean_ctor_get(v_v_4841_, 1);
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
                        1 => match crate::leanh::lean_obj_tag(v_u_4840_) {
                            2 => {
                                v_a_4870_ = crate::leanh::lean_ctor_get(v_u_4840_, 0);
                                v_a_4871_ = crate::leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_u2081_4859_ = v_a_4870_;
                                v_u_u2082_4860_ = v_a_4871_;
                                v_v_4861_ = v_v_4841_;
                                state = 4;
                                continue;
                            }
                            3 => {
                                v_a_4872_ = crate::leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_4840_ = v_a_4872_;
                                state = 0;
                                continue;
                            }
                            1 => {
                                v_a_4874_ = crate::leanh::lean_ctor_get(v_v_4841_, 0);
                                v_a_4875_ = crate::leanh::lean_ctor_get(v_u_4840_, 0);
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
                        _ => match crate::leanh::lean_obj_tag(v_u_4840_) {
                            2 => {
                                v_a_4877_ = crate::leanh::lean_ctor_get(v_u_4840_, 0);
                                v_a_4878_ = crate::leanh::lean_ctor_get(v_u_4840_, 1);
                                v_u_u2081_4859_ = v_a_4877_;
                                v_u_u2082_4860_ = v_a_4878_;
                                v_v_4861_ = v_v_4841_;
                                state = 4;
                                continue;
                            }
                            3 => {
                                v_a_4879_ = crate::leanh::lean_ctor_get(v_u_4840_, 1);
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
                    crate::leanh::lean_dec(v___x_4845_);
                    crate::leanh::lean_dec(v___x_4844_);
                    return v___x_4846_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_v_4841_) == 3 {
                    v_a_4848_ = crate::leanh::lean_ctor_get(v_v_4841_, 0);
                    v_a_4849_ = crate::leanh::lean_ctor_get(v_v_4841_, 1);
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
                    crate::leanh::lean_dec(v___x_4853_);
                    if v___x_4854_ == 0 {
                        v___x_4855_ = l_Lean_Level_isZero(v_v_x27_4852_);
                        crate::leanh::lean_dec(v_v_x27_4852_);
                        v___y_4843_ = v___x_4855_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_x27_4852_);
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
    mut v_u_4881_: *mut crate::leanh::LeanObject,
    mut v_v_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4883_: u8 = 0;
    let mut v_r_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4883_ = l___private_Lean_Level_0__Lean_Level_geq_go(v_u_4881_, v_v_4882_);
    crate::leanh::lean_dec(v_v_4882_);
    crate::leanh::lean_dec(v_u_4881_);
    v_r_4884_ = crate::leanh::lean_box((v_res_4883_) as usize);
    return v_r_4884_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter___redArg(
    mut v_u_4885_: *mut crate::leanh::LeanObject,
    mut v_v_4886_: *mut crate::leanh::LeanObject,
    mut v_h__1_4887_: *mut crate::leanh::LeanObject,
    mut v_h__2_4888_: *mut crate::leanh::LeanObject,
    mut v_h__3_4889_: *mut crate::leanh::LeanObject,
    mut v_h__4_4890_: *mut crate::leanh::LeanObject,
    mut v_h__5_4891_: *mut crate::leanh::LeanObject,
    mut v_h__6_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_v_4886_) {
        0 => {
            let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4892_);
            crate::leanh::lean_dec(v_h__5_4891_);
            crate::leanh::lean_dec(v_h__4_4890_);
            crate::leanh::lean_dec(v_h__3_4889_);
            crate::leanh::lean_dec(v_h__2_4888_);
            v___x_4893_ = crate::leanh::lean_apply_1(v_h__1_4887_, v_u_4885_);
            return v___x_4893_;
        }
        2 => {
            let mut v_a_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4892_);
            crate::leanh::lean_dec(v_h__5_4891_);
            crate::leanh::lean_dec(v_h__4_4890_);
            crate::leanh::lean_dec(v_h__3_4889_);
            crate::leanh::lean_dec(v_h__1_4887_);
            v_a_4894_ = crate::leanh::lean_ctor_get(v_v_4886_, 0);
            crate::leanh::lean_inc(v_a_4894_);
            v_a_4895_ = crate::leanh::lean_ctor_get(v_v_4886_, 1);
            crate::leanh::lean_inc(v_a_4895_);
            crate::leanh::lean_dec_ref_known(v_v_4886_, 2);
            v___x_4896_ = crate::leanh::lean_apply_3(v_h__2_4888_, v_u_4885_, v_a_4894_, v_a_4895_);
            return v___x_4896_;
        }
        1 => {
            crate::leanh::lean_dec(v_h__2_4888_);
            crate::leanh::lean_dec(v_h__1_4887_);
            match crate::leanh::lean_obj_tag(v_u_4885_) {
                2 => {
                    let mut v_a_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4892_);
                    crate::leanh::lean_dec(v_h__5_4891_);
                    crate::leanh::lean_dec(v_h__4_4890_);
                    v_a_4897_ = crate::leanh::lean_ctor_get(v_u_4885_, 0);
                    crate::leanh::lean_inc(v_a_4897_);
                    v_a_4898_ = crate::leanh::lean_ctor_get(v_u_4885_, 1);
                    crate::leanh::lean_inc(v_a_4898_);
                    crate::leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4899_ = crate::leanh::lean_apply_5(
                        v_h__3_4889_,
                        v_a_4897_,
                        v_a_4898_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4899_;
                }
                3 => {
                    let mut v_a_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4892_);
                    crate::leanh::lean_dec(v_h__5_4891_);
                    crate::leanh::lean_dec(v_h__3_4889_);
                    v_a_4900_ = crate::leanh::lean_ctor_get(v_u_4885_, 0);
                    crate::leanh::lean_inc(v_a_4900_);
                    v_a_4901_ = crate::leanh::lean_ctor_get(v_u_4885_, 1);
                    crate::leanh::lean_inc(v_a_4901_);
                    crate::leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4902_ = crate::leanh::lean_apply_5(
                        v_h__4_4890_,
                        v_a_4900_,
                        v_a_4901_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4902_;
                }
                1 => {
                    let mut v_a_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4892_);
                    crate::leanh::lean_dec(v_h__4_4890_);
                    crate::leanh::lean_dec(v_h__3_4889_);
                    v_a_4903_ = crate::leanh::lean_ctor_get(v_v_4886_, 0);
                    crate::leanh::lean_inc(v_a_4903_);
                    crate::leanh::lean_dec_ref_known(v_v_4886_, 1);
                    v_a_4904_ = crate::leanh::lean_ctor_get(v_u_4885_, 0);
                    crate::leanh::lean_inc(v_a_4904_);
                    crate::leanh::lean_dec_ref_known(v_u_4885_, 1);
                    v___x_4905_ = crate::leanh::lean_apply_2(v_h__5_4891_, v_a_4904_, v_a_4903_);
                    return v___x_4905_;
                }
                _ => {
                    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4891_);
                    crate::leanh::lean_dec(v_h__4_4890_);
                    crate::leanh::lean_dec(v_h__3_4889_);
                    v___x_4906_ = crate::leanh::lean_apply_7(
                        v_h__6_4892_,
                        v_u_4885_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4906_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__5_4891_);
            crate::leanh::lean_dec(v_h__2_4888_);
            crate::leanh::lean_dec(v_h__1_4887_);
            match crate::leanh::lean_obj_tag(v_u_4885_) {
                2 => {
                    let mut v_a_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4892_);
                    crate::leanh::lean_dec(v_h__4_4890_);
                    v_a_4907_ = crate::leanh::lean_ctor_get(v_u_4885_, 0);
                    crate::leanh::lean_inc(v_a_4907_);
                    v_a_4908_ = crate::leanh::lean_ctor_get(v_u_4885_, 1);
                    crate::leanh::lean_inc(v_a_4908_);
                    crate::leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4909_ = crate::leanh::lean_apply_5(
                        v_h__3_4889_,
                        v_a_4907_,
                        v_a_4908_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4909_;
                }
                3 => {
                    let mut v_a_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4892_);
                    crate::leanh::lean_dec(v_h__3_4889_);
                    v_a_4910_ = crate::leanh::lean_ctor_get(v_u_4885_, 0);
                    crate::leanh::lean_inc(v_a_4910_);
                    v_a_4911_ = crate::leanh::lean_ctor_get(v_u_4885_, 1);
                    crate::leanh::lean_inc(v_a_4911_);
                    crate::leanh::lean_dec_ref_known(v_u_4885_, 2);
                    v___x_4912_ = crate::leanh::lean_apply_5(
                        v_h__4_4890_,
                        v_a_4910_,
                        v_a_4911_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4912_;
                }
                _ => {
                    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4890_);
                    crate::leanh::lean_dec(v_h__3_4889_);
                    v___x_4913_ = crate::leanh::lean_apply_7(
                        v_h__6_4892_,
                        v_u_4885_,
                        v_v_4886_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4913_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_geq_go_match__1_splitter(
    mut v_motive_4914_: *mut crate::leanh::LeanObject,
    mut v_u_4915_: *mut crate::leanh::LeanObject,
    mut v_v_4916_: *mut crate::leanh::LeanObject,
    mut v_h__1_4917_: *mut crate::leanh::LeanObject,
    mut v_h__2_4918_: *mut crate::leanh::LeanObject,
    mut v_h__3_4919_: *mut crate::leanh::LeanObject,
    mut v_h__4_4920_: *mut crate::leanh::LeanObject,
    mut v_h__5_4921_: *mut crate::leanh::LeanObject,
    mut v_h__6_4922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_v_4916_) {
        0 => {
            let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4922_);
            crate::leanh::lean_dec(v_h__5_4921_);
            crate::leanh::lean_dec(v_h__4_4920_);
            crate::leanh::lean_dec(v_h__3_4919_);
            crate::leanh::lean_dec(v_h__2_4918_);
            v___x_4923_ = crate::leanh::lean_apply_1(v_h__1_4917_, v_u_4915_);
            return v___x_4923_;
        }
        2 => {
            let mut v_a_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__6_4922_);
            crate::leanh::lean_dec(v_h__5_4921_);
            crate::leanh::lean_dec(v_h__4_4920_);
            crate::leanh::lean_dec(v_h__3_4919_);
            crate::leanh::lean_dec(v_h__1_4917_);
            v_a_4924_ = crate::leanh::lean_ctor_get(v_v_4916_, 0);
            crate::leanh::lean_inc(v_a_4924_);
            v_a_4925_ = crate::leanh::lean_ctor_get(v_v_4916_, 1);
            crate::leanh::lean_inc(v_a_4925_);
            crate::leanh::lean_dec_ref_known(v_v_4916_, 2);
            v___x_4926_ = crate::leanh::lean_apply_3(v_h__2_4918_, v_u_4915_, v_a_4924_, v_a_4925_);
            return v___x_4926_;
        }
        1 => {
            crate::leanh::lean_dec(v_h__2_4918_);
            crate::leanh::lean_dec(v_h__1_4917_);
            match crate::leanh::lean_obj_tag(v_u_4915_) {
                2 => {
                    let mut v_a_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4922_);
                    crate::leanh::lean_dec(v_h__5_4921_);
                    crate::leanh::lean_dec(v_h__4_4920_);
                    v_a_4927_ = crate::leanh::lean_ctor_get(v_u_4915_, 0);
                    crate::leanh::lean_inc(v_a_4927_);
                    v_a_4928_ = crate::leanh::lean_ctor_get(v_u_4915_, 1);
                    crate::leanh::lean_inc(v_a_4928_);
                    crate::leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4929_ = crate::leanh::lean_apply_5(
                        v_h__3_4919_,
                        v_a_4927_,
                        v_a_4928_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4929_;
                }
                3 => {
                    let mut v_a_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4922_);
                    crate::leanh::lean_dec(v_h__5_4921_);
                    crate::leanh::lean_dec(v_h__3_4919_);
                    v_a_4930_ = crate::leanh::lean_ctor_get(v_u_4915_, 0);
                    crate::leanh::lean_inc(v_a_4930_);
                    v_a_4931_ = crate::leanh::lean_ctor_get(v_u_4915_, 1);
                    crate::leanh::lean_inc(v_a_4931_);
                    crate::leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4932_ = crate::leanh::lean_apply_5(
                        v_h__4_4920_,
                        v_a_4930_,
                        v_a_4931_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4932_;
                }
                1 => {
                    let mut v_a_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4922_);
                    crate::leanh::lean_dec(v_h__4_4920_);
                    crate::leanh::lean_dec(v_h__3_4919_);
                    v_a_4933_ = crate::leanh::lean_ctor_get(v_v_4916_, 0);
                    crate::leanh::lean_inc(v_a_4933_);
                    crate::leanh::lean_dec_ref_known(v_v_4916_, 1);
                    v_a_4934_ = crate::leanh::lean_ctor_get(v_u_4915_, 0);
                    crate::leanh::lean_inc(v_a_4934_);
                    crate::leanh::lean_dec_ref_known(v_u_4915_, 1);
                    v___x_4935_ = crate::leanh::lean_apply_2(v_h__5_4921_, v_a_4934_, v_a_4933_);
                    return v___x_4935_;
                }
                _ => {
                    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_4921_);
                    crate::leanh::lean_dec(v_h__4_4920_);
                    crate::leanh::lean_dec(v_h__3_4919_);
                    v___x_4936_ = crate::leanh::lean_apply_7(
                        v_h__6_4922_,
                        v_u_4915_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4936_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__5_4921_);
            crate::leanh::lean_dec(v_h__2_4918_);
            crate::leanh::lean_dec(v_h__1_4917_);
            match crate::leanh::lean_obj_tag(v_u_4915_) {
                2 => {
                    let mut v_a_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4922_);
                    crate::leanh::lean_dec(v_h__4_4920_);
                    v_a_4937_ = crate::leanh::lean_ctor_get(v_u_4915_, 0);
                    crate::leanh::lean_inc(v_a_4937_);
                    v_a_4938_ = crate::leanh::lean_ctor_get(v_u_4915_, 1);
                    crate::leanh::lean_inc(v_a_4938_);
                    crate::leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4939_ = crate::leanh::lean_apply_5(
                        v_h__3_4919_,
                        v_a_4937_,
                        v_a_4938_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4939_;
                }
                3 => {
                    let mut v_a_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_4922_);
                    crate::leanh::lean_dec(v_h__3_4919_);
                    v_a_4940_ = crate::leanh::lean_ctor_get(v_u_4915_, 0);
                    crate::leanh::lean_inc(v_a_4940_);
                    v_a_4941_ = crate::leanh::lean_ctor_get(v_u_4915_, 1);
                    crate::leanh::lean_inc(v_a_4941_);
                    crate::leanh::lean_dec_ref_known(v_u_4915_, 2);
                    v___x_4942_ = crate::leanh::lean_apply_5(
                        v_h__4_4920_,
                        v_a_4940_,
                        v_a_4941_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4942_;
                }
                _ => {
                    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_4920_);
                    crate::leanh::lean_dec(v_h__3_4919_);
                    v___x_4943_ = crate::leanh::lean_apply_7(
                        v_h__6_4922_,
                        v_u_4915_,
                        v_v_4916_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4943_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter___redArg(
    mut v_x_4944_: *mut crate::leanh::LeanObject,
    mut v_h__1_4945_: *mut crate::leanh::LeanObject,
    mut v_h__2_4946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4944_) == 3 {
        let mut v_a_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4946_);
        v_a_4947_ = crate::leanh::lean_ctor_get(v_x_4944_, 0);
        crate::leanh::lean_inc(v_a_4947_);
        v_a_4948_ = crate::leanh::lean_ctor_get(v_x_4944_, 1);
        crate::leanh::lean_inc(v_a_4948_);
        crate::leanh::lean_dec_ref_known(v_x_4944_, 2);
        v___x_4949_ = crate::leanh::lean_apply_2(v_h__1_4945_, v_a_4947_, v_a_4948_);
        return v___x_4949_;
    } else {
        let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4945_);
        v___x_4950_ =
            crate::leanh::lean_apply_2(v_h__2_4946_, v_x_4944_, crate::leanh::lean_box(0));
        return v___x_4950_;
    }
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_isIMax_match__1_splitter(
    mut v_motive_4951_: *mut crate::leanh::LeanObject,
    mut v_x_4952_: *mut crate::leanh::LeanObject,
    mut v_h__1_4953_: *mut crate::leanh::LeanObject,
    mut v_h__2_4954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4952_) == 3 {
        let mut v_a_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_4954_);
        v_a_4955_ = crate::leanh::lean_ctor_get(v_x_4952_, 0);
        crate::leanh::lean_inc(v_a_4955_);
        v_a_4956_ = crate::leanh::lean_ctor_get(v_x_4952_, 1);
        crate::leanh::lean_inc(v_a_4956_);
        crate::leanh::lean_dec_ref_known(v_x_4952_, 2);
        v___x_4957_ = crate::leanh::lean_apply_2(v_h__1_4953_, v_a_4955_, v_a_4956_);
        return v___x_4957_;
    } else {
        let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_4953_);
        v___x_4958_ =
            crate::leanh::lean_apply_2(v_h__2_4954_, v_x_4952_, crate::leanh::lean_box(0));
        return v___x_4958_;
    }
}
pub unsafe fn l_Lean_Level_geq(
    mut v_u_4959_: *mut crate::leanh::LeanObject,
    mut v_v_4960_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: u8 = 0;
    v___x_4961_ = l_Lean_Level_normalize(v_u_4959_);
    v___x_4962_ = l_Lean_Level_normalize(v_v_4960_);
    v___x_4963_ = l___private_Lean_Level_0__Lean_Level_geq_go(v___x_4961_, v___x_4962_);
    crate::leanh::lean_dec(v___x_4962_);
    crate::leanh::lean_dec(v___x_4961_);
    return v___x_4963_;
}
pub unsafe fn l_Lean_Level_geq___boxed(
    mut v_u_4964_: *mut crate::leanh::LeanObject,
    mut v_v_4965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4966_: u8 = 0;
    let mut v_r_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4966_ = l_Lean_Level_geq(v_u_4964_, v_v_4965_);
    crate::leanh::lean_dec(v_v_4965_);
    crate::leanh::lean_dec(v_u_4964_);
    v_r_4967_ = crate::leanh::lean_box((v_res_4966_) as usize);
    return v_r_4967_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(
    mut v_k_4968_: *mut crate::leanh::LeanObject,
    mut v_v_4969_: *mut crate::leanh::LeanObject,
    mut v_t_4970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4978_: u8 = 0;
    let mut v___x_4979_: u8 = 0;
    let mut v_impl_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v_size_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: u8 = 0;
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5010_: u8 = 0;
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5036_: u8 = 0;
    let mut v_unused_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5050_: u8 = 0;
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5054_: u8 = 0;
    let mut v_unused_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5061_: u8 = 0;
    let mut v_unused_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5073_: u8 = 0;
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5081_: u8 = 0;
    let mut v_unused_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5089_: u8 = 0;
    let mut v_k_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5094_: u8 = 0;
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5105_: u8 = 0;
    let mut v_unused_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: u8 = 0;
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5138_: u8 = 0;
    let mut v_size_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: u8 = 0;
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5175_: u8 = 0;
    let mut v_unused_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5188_: u8 = 0;
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5192_: u8 = 0;
    let mut v_unused_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5199_: u8 = 0;
    let mut v_unused_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5211_: u8 = 0;
    let mut v_k_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5216_: u8 = 0;
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5227_: u8 = 0;
    let mut v_unused_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5231_: u8 = 0;
    let mut v_unused_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5239_: u8 = 0;
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5247_: u8 = 0;
    let mut v_unused_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5255_: u8 = 0;
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_4970_) == 0 {
                    v_size_4971_ = crate::leanh::lean_ctor_get(v_t_4970_, 0);
                    v_k_4972_ = crate::leanh::lean_ctor_get(v_t_4970_, 1);
                    v_v_4973_ = crate::leanh::lean_ctor_get(v_t_4970_, 2);
                    v_l_4974_ = crate::leanh::lean_ctor_get(v_t_4970_, 3);
                    v_r_4975_ = crate::leanh::lean_ctor_get(v_t_4970_, 4);
                    v_isSharedCheck_5255_ = (!crate::leanh::lean_is_exclusive(v_t_4970_)) as u8;
                    if v_isSharedCheck_5255_ == 0 {
                        v___x_4977_ = v_t_4970_;
                        v_isShared_4978_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_4975_);
                        crate::leanh::lean_inc(v_l_4974_);
                        crate::leanh::lean_inc(v_v_4973_);
                        crate::leanh::lean_inc(v_k_4972_);
                        crate::leanh::lean_inc(v_size_4971_);
                        crate::leanh::lean_dec(v_t_4970_);
                        v___x_4977_ = crate::leanh::lean_box(0);
                        v_isShared_4978_ = v_isSharedCheck_5255_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_5256_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5257_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5257_, 0, v___x_5256_);
                    crate::leanh::lean_ctor_set(v___x_5257_, 1, v_k_4968_);
                    crate::leanh::lean_ctor_set(v___x_5257_, 2, v_v_4969_);
                    crate::leanh::lean_ctor_set(v___x_5257_, 3, v_t_4970_);
                    crate::leanh::lean_ctor_set(v___x_5257_, 4, v_t_4970_);
                    return v___x_5257_;
                }
            }
            1 => {
                v___x_4979_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4968_, v_k_4972_);
                match v___x_4979_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_4971_);
                        v_impl_4980_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_4968_, v_v_4969_, v_l_4974_);
                        v___x_4981_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_4975_) == 0 {
                            v_size_4982_ = crate::leanh::lean_ctor_get(v_r_4975_, 0);
                            v_size_4983_ = crate::leanh::lean_ctor_get(v_impl_4980_, 0);
                            crate::leanh::lean_inc(v_size_4983_);
                            v_k_4984_ = crate::leanh::lean_ctor_get(v_impl_4980_, 1);
                            crate::leanh::lean_inc(v_k_4984_);
                            v_v_4985_ = crate::leanh::lean_ctor_get(v_impl_4980_, 2);
                            crate::leanh::lean_inc(v_v_4985_);
                            v_l_4986_ = crate::leanh::lean_ctor_get(v_impl_4980_, 3);
                            crate::leanh::lean_inc(v_l_4986_);
                            v_r_4987_ = crate::leanh::lean_ctor_get(v_impl_4980_, 4);
                            crate::leanh::lean_inc(v_r_4987_);
                            v___x_4988_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4989_ = lean_nat_mul(v___x_4988_, v_size_4982_);
                            v___x_4990_ = lean_nat_dec_lt(v___x_4989_, v_size_4983_);
                            crate::leanh::lean_dec(v___x_4989_);
                            if v___x_4990_ == 0 {
                                crate::leanh::lean_dec(v_r_4987_);
                                crate::leanh::lean_dec(v_l_4986_);
                                crate::leanh::lean_dec(v_v_4985_);
                                crate::leanh::lean_dec(v_k_4984_);
                                v___x_4991_ = lean_nat_add(v___x_4981_, v_size_4983_);
                                crate::leanh::lean_dec(v_size_4983_);
                                v___x_4992_ = lean_nat_add(v___x_4991_, v_size_4982_);
                                crate::leanh::lean_dec(v___x_4991_);
                                if v_isShared_4978_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v_impl_4980_);
                                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_4992_);
                                    v___x_4994_ = v___x_4977_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4995_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        0,
                                        v___x_4992_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        1,
                                        v_k_4972_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        2,
                                        v_v_4973_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4995_,
                                        3,
                                        v_impl_4980_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                if v_isSharedCheck_5061_ == 0 {
                                    v_unused_5062_ = crate::leanh::lean_ctor_get(v_impl_4980_, 4);
                                    crate::leanh::lean_dec(v_unused_5062_);
                                    v_unused_5063_ = crate::leanh::lean_ctor_get(v_impl_4980_, 3);
                                    crate::leanh::lean_dec(v_unused_5063_);
                                    v_unused_5064_ = crate::leanh::lean_ctor_get(v_impl_4980_, 2);
                                    crate::leanh::lean_dec(v_unused_5064_);
                                    v_unused_5065_ = crate::leanh::lean_ctor_get(v_impl_4980_, 1);
                                    crate::leanh::lean_dec(v_unused_5065_);
                                    v_unused_5066_ = crate::leanh::lean_ctor_get(v_impl_4980_, 0);
                                    crate::leanh::lean_dec(v_unused_5066_);
                                    v___x_4997_ = v_impl_4980_;
                                    v_isShared_4998_ = v_isSharedCheck_5061_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_4980_);
                                    v___x_4997_ = crate::leanh::lean_box(0);
                                    v_isShared_4998_ = v_isSharedCheck_5061_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_5067_ = crate::leanh::lean_ctor_get(v_impl_4980_, 3);
                            crate::leanh::lean_inc(v_l_5067_);
                            if crate::leanh::lean_obj_tag(v_l_5067_) == 0 {
                                v_r_5068_ = crate::leanh::lean_ctor_get(v_impl_4980_, 4);
                                v_k_5069_ = crate::leanh::lean_ctor_get(v_impl_4980_, 1);
                                v_v_5070_ = crate::leanh::lean_ctor_get(v_impl_4980_, 2);
                                v_isSharedCheck_5081_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                if v_isSharedCheck_5081_ == 0 {
                                    v_unused_5082_ = crate::leanh::lean_ctor_get(v_impl_4980_, 3);
                                    crate::leanh::lean_dec(v_unused_5082_);
                                    v_unused_5083_ = crate::leanh::lean_ctor_get(v_impl_4980_, 0);
                                    crate::leanh::lean_dec(v_unused_5083_);
                                    v___x_5072_ = v_impl_4980_;
                                    v_isShared_5073_ = v_isSharedCheck_5081_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_5068_);
                                    crate::leanh::lean_inc(v_v_5070_);
                                    crate::leanh::lean_inc(v_k_5069_);
                                    crate::leanh::lean_dec(v_impl_4980_);
                                    v___x_5072_ = crate::leanh::lean_box(0);
                                    v_isShared_5073_ = v_isSharedCheck_5081_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_5084_ = crate::leanh::lean_ctor_get(v_impl_4980_, 4);
                                crate::leanh::lean_inc(v_r_5084_);
                                if crate::leanh::lean_obj_tag(v_r_5084_) == 0 {
                                    v_k_5085_ = crate::leanh::lean_ctor_get(v_impl_4980_, 1);
                                    v_v_5086_ = crate::leanh::lean_ctor_get(v_impl_4980_, 2);
                                    v_isSharedCheck_5109_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_4980_)) as u8;
                                    if v_isSharedCheck_5109_ == 0 {
                                        v_unused_5110_ =
                                            crate::leanh::lean_ctor_get(v_impl_4980_, 4);
                                        crate::leanh::lean_dec(v_unused_5110_);
                                        v_unused_5111_ =
                                            crate::leanh::lean_ctor_get(v_impl_4980_, 3);
                                        crate::leanh::lean_dec(v_unused_5111_);
                                        v_unused_5112_ =
                                            crate::leanh::lean_ctor_get(v_impl_4980_, 0);
                                        crate::leanh::lean_dec(v_unused_5112_);
                                        v___x_5088_ = v_impl_4980_;
                                        v_isShared_5089_ = v_isSharedCheck_5109_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_5086_);
                                        crate::leanh::lean_inc(v_k_5085_);
                                        crate::leanh::lean_dec(v_impl_4980_);
                                        v___x_5088_ = crate::leanh::lean_box(0);
                                        v_isShared_5089_ = v_isSharedCheck_5109_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_5113_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4978_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4977_, 4, v_r_5084_);
                                        crate::leanh::lean_ctor_set(v___x_4977_, 3, v_impl_4980_);
                                        crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5113_);
                                        v___x_5115_ = v___x_4977_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5116_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            0,
                                            v___x_5113_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            1,
                                            v_k_4972_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            2,
                                            v_v_4973_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5116_,
                                            3,
                                            v_impl_4980_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                        crate::leanh::lean_dec(v_v_4973_);
                        crate::leanh::lean_dec(v_k_4972_);
                        if v_isShared_4978_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_4969_);
                            crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_4968_);
                            v___x_5118_ = v___x_4977_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_5119_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 0, v_size_4971_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 1, v_k_4968_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 2, v_v_4969_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 3, v_l_4974_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5119_, 4, v_r_4975_);
                            v___x_5118_ = v_reuseFailAlloc_5119_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_4971_);
                        v_impl_5120_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_k_4968_, v_v_4969_, v_r_4975_);
                        v___x_5121_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_4974_) == 0 {
                            v_size_5122_ = crate::leanh::lean_ctor_get(v_l_4974_, 0);
                            v_size_5123_ = crate::leanh::lean_ctor_get(v_impl_5120_, 0);
                            crate::leanh::lean_inc(v_size_5123_);
                            v_k_5124_ = crate::leanh::lean_ctor_get(v_impl_5120_, 1);
                            crate::leanh::lean_inc(v_k_5124_);
                            v_v_5125_ = crate::leanh::lean_ctor_get(v_impl_5120_, 2);
                            crate::leanh::lean_inc(v_v_5125_);
                            v_l_5126_ = crate::leanh::lean_ctor_get(v_impl_5120_, 3);
                            crate::leanh::lean_inc(v_l_5126_);
                            v_r_5127_ = crate::leanh::lean_ctor_get(v_impl_5120_, 4);
                            crate::leanh::lean_inc(v_r_5127_);
                            v___x_5128_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_5129_ = lean_nat_mul(v___x_5128_, v_size_5122_);
                            v___x_5130_ = lean_nat_dec_lt(v___x_5129_, v_size_5123_);
                            crate::leanh::lean_dec(v___x_5129_);
                            if v___x_5130_ == 0 {
                                crate::leanh::lean_dec(v_r_5127_);
                                crate::leanh::lean_dec(v_l_5126_);
                                crate::leanh::lean_dec(v_v_5125_);
                                crate::leanh::lean_dec(v_k_5124_);
                                v___x_5131_ = lean_nat_add(v___x_5121_, v_size_5122_);
                                v___x_5132_ = lean_nat_add(v___x_5131_, v_size_5123_);
                                crate::leanh::lean_dec(v_size_5123_);
                                crate::leanh::lean_dec(v___x_5131_);
                                if v_isShared_4978_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v_impl_5120_);
                                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5132_);
                                    v___x_5134_ = v___x_4977_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_5135_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        0,
                                        v___x_5132_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        1,
                                        v_k_4972_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        2,
                                        v_v_4973_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_5135_,
                                        3,
                                        v_l_4974_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                    (!crate::leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                if v_isSharedCheck_5199_ == 0 {
                                    v_unused_5200_ = crate::leanh::lean_ctor_get(v_impl_5120_, 4);
                                    crate::leanh::lean_dec(v_unused_5200_);
                                    v_unused_5201_ = crate::leanh::lean_ctor_get(v_impl_5120_, 3);
                                    crate::leanh::lean_dec(v_unused_5201_);
                                    v_unused_5202_ = crate::leanh::lean_ctor_get(v_impl_5120_, 2);
                                    crate::leanh::lean_dec(v_unused_5202_);
                                    v_unused_5203_ = crate::leanh::lean_ctor_get(v_impl_5120_, 1);
                                    crate::leanh::lean_dec(v_unused_5203_);
                                    v_unused_5204_ = crate::leanh::lean_ctor_get(v_impl_5120_, 0);
                                    crate::leanh::lean_dec(v_unused_5204_);
                                    v___x_5137_ = v_impl_5120_;
                                    v_isShared_5138_ = v_isSharedCheck_5199_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_5120_);
                                    v___x_5137_ = crate::leanh::lean_box(0);
                                    v_isShared_5138_ = v_isSharedCheck_5199_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_5205_ = crate::leanh::lean_ctor_get(v_impl_5120_, 3);
                            crate::leanh::lean_inc(v_l_5205_);
                            if crate::leanh::lean_obj_tag(v_l_5205_) == 0 {
                                v_r_5206_ = crate::leanh::lean_ctor_get(v_impl_5120_, 4);
                                v_k_5207_ = crate::leanh::lean_ctor_get(v_impl_5120_, 1);
                                v_v_5208_ = crate::leanh::lean_ctor_get(v_impl_5120_, 2);
                                v_isSharedCheck_5231_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                if v_isSharedCheck_5231_ == 0 {
                                    v_unused_5232_ = crate::leanh::lean_ctor_get(v_impl_5120_, 3);
                                    crate::leanh::lean_dec(v_unused_5232_);
                                    v_unused_5233_ = crate::leanh::lean_ctor_get(v_impl_5120_, 0);
                                    crate::leanh::lean_dec(v_unused_5233_);
                                    v___x_5210_ = v_impl_5120_;
                                    v_isShared_5211_ = v_isSharedCheck_5231_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_5206_);
                                    crate::leanh::lean_inc(v_v_5208_);
                                    crate::leanh::lean_inc(v_k_5207_);
                                    crate::leanh::lean_dec(v_impl_5120_);
                                    v___x_5210_ = crate::leanh::lean_box(0);
                                    v_isShared_5211_ = v_isSharedCheck_5231_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_5234_ = crate::leanh::lean_ctor_get(v_impl_5120_, 4);
                                crate::leanh::lean_inc(v_r_5234_);
                                if crate::leanh::lean_obj_tag(v_r_5234_) == 0 {
                                    v_k_5235_ = crate::leanh::lean_ctor_get(v_impl_5120_, 1);
                                    v_v_5236_ = crate::leanh::lean_ctor_get(v_impl_5120_, 2);
                                    v_isSharedCheck_5247_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_5120_)) as u8;
                                    if v_isSharedCheck_5247_ == 0 {
                                        v_unused_5248_ =
                                            crate::leanh::lean_ctor_get(v_impl_5120_, 4);
                                        crate::leanh::lean_dec(v_unused_5248_);
                                        v_unused_5249_ =
                                            crate::leanh::lean_ctor_get(v_impl_5120_, 3);
                                        crate::leanh::lean_dec(v_unused_5249_);
                                        v_unused_5250_ =
                                            crate::leanh::lean_ctor_get(v_impl_5120_, 0);
                                        crate::leanh::lean_dec(v_unused_5250_);
                                        v___x_5238_ = v_impl_5120_;
                                        v_isShared_5239_ = v_isSharedCheck_5247_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_5236_);
                                        crate::leanh::lean_inc(v_k_5235_);
                                        crate::leanh::lean_dec(v_impl_5120_);
                                        v___x_5238_ = crate::leanh::lean_box(0);
                                        v_isShared_5239_ = v_isSharedCheck_5247_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_5251_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_4978_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_4977_, 4, v_impl_5120_);
                                        crate::leanh::lean_ctor_set(v___x_4977_, 3, v_r_5234_);
                                        crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5251_);
                                        v___x_5253_ = v___x_4977_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_5254_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            0,
                                            v___x_5251_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            1,
                                            v_k_4972_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            2,
                                            v_v_4973_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_5254_,
                                            3,
                                            v_r_5234_,
                                        );
                                        crate::leanh::lean_ctor_set(
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
                v_size_4999_ = crate::leanh::lean_ctor_get(v_l_4986_, 0);
                v_size_5000_ = crate::leanh::lean_ctor_get(v_r_4987_, 0);
                v_k_5001_ = crate::leanh::lean_ctor_get(v_r_4987_, 1);
                v_v_5002_ = crate::leanh::lean_ctor_get(v_r_4987_, 2);
                v_l_5003_ = crate::leanh::lean_ctor_get(v_r_4987_, 3);
                v_r_5004_ = crate::leanh::lean_ctor_get(v_r_4987_, 4);
                v___x_5005_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5006_ = lean_nat_mul(v___x_5005_, v_size_4999_);
                v___x_5007_ = lean_nat_dec_lt(v_size_5000_, v___x_5006_);
                crate::leanh::lean_dec(v___x_5006_);
                if v___x_5007_ == 0 {
                    crate::leanh::lean_inc(v_r_5004_);
                    crate::leanh::lean_inc(v_l_5003_);
                    crate::leanh::lean_inc(v_v_5002_);
                    crate::leanh::lean_inc(v_k_5001_);
                    v_isSharedCheck_5036_ = (!crate::leanh::lean_is_exclusive(v_r_4987_)) as u8;
                    if v_isSharedCheck_5036_ == 0 {
                        v_unused_5037_ = crate::leanh::lean_ctor_get(v_r_4987_, 4);
                        crate::leanh::lean_dec(v_unused_5037_);
                        v_unused_5038_ = crate::leanh::lean_ctor_get(v_r_4987_, 3);
                        crate::leanh::lean_dec(v_unused_5038_);
                        v_unused_5039_ = crate::leanh::lean_ctor_get(v_r_4987_, 2);
                        crate::leanh::lean_dec(v_unused_5039_);
                        v_unused_5040_ = crate::leanh::lean_ctor_get(v_r_4987_, 1);
                        crate::leanh::lean_dec(v_unused_5040_);
                        v_unused_5041_ = crate::leanh::lean_ctor_get(v_r_4987_, 0);
                        crate::leanh::lean_dec(v_unused_5041_);
                        v___x_5009_ = v_r_4987_;
                        v_isShared_5010_ = v_isSharedCheck_5036_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_4987_);
                        v___x_5009_ = crate::leanh::lean_box(0);
                        v_isShared_5010_ = v_isSharedCheck_5036_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4977_);
                    v___x_5042_ = lean_nat_add(v___x_4981_, v_size_4983_);
                    crate::leanh::lean_dec(v_size_4983_);
                    v___x_5043_ = lean_nat_add(v___x_5042_, v_size_4982_);
                    crate::leanh::lean_dec(v___x_5042_);
                    v___x_5044_ = lean_nat_add(v___x_4981_, v_size_4982_);
                    v___x_5045_ = lean_nat_add(v___x_5044_, v_size_5000_);
                    crate::leanh::lean_dec(v___x_5044_);
                    crate::leanh::lean_inc_ref(v_r_4975_);
                    if v_isShared_4998_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4997_, 4, v_r_4975_);
                        crate::leanh::lean_ctor_set(v___x_4997_, 3, v_r_4987_);
                        crate::leanh::lean_ctor_set(v___x_4997_, 2, v_v_4973_);
                        crate::leanh::lean_ctor_set(v___x_4997_, 1, v_k_4972_);
                        crate::leanh::lean_ctor_set(v___x_4997_, 0, v___x_5045_);
                        v___x_5047_ = v___x_4997_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_5060_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 0, v___x_5045_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 1, v_k_4972_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 2, v_v_4973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 3, v_r_4987_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5060_, 4, v_r_4975_);
                        v___x_5047_ = v_reuseFailAlloc_5060_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5011_ = lean_nat_add(v___x_4981_, v_size_4983_);
                crate::leanh::lean_dec(v_size_4983_);
                v___x_5012_ = lean_nat_add(v___x_5011_, v_size_4982_);
                crate::leanh::lean_dec(v___x_5011_);
                v___x_5024_ = lean_nat_add(v___x_4981_, v_size_4999_);
                if crate::leanh::lean_obj_tag(v_l_5003_) == 0 {
                    v_size_5034_ = crate::leanh::lean_ctor_get(v_l_5003_, 0);
                    crate::leanh::lean_inc(v_size_5034_);
                    v___y_5026_ = v_size_5034_;
                    state = 8;
                    continue;
                } else {
                    v___x_5035_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5026_ = v___x_5035_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_5017_ = lean_nat_add(v___y_5015_, v___y_5016_);
                crate::leanh::lean_dec(v___y_5016_);
                crate::leanh::lean_dec(v___y_5015_);
                if v_isShared_5010_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5009_, 4, v_r_4975_);
                    crate::leanh::lean_ctor_set(v___x_5009_, 3, v_r_5004_);
                    crate::leanh::lean_ctor_set(v___x_5009_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v___x_5009_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v___x_5009_, 0, v___x_5017_);
                    v___x_5019_ = v___x_5009_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5023_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 0, v___x_5017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 3, v_r_5004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5023_, 4, v_r_4975_);
                    v___x_5019_ = v_reuseFailAlloc_5023_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4997_, 4, v___x_5019_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 3, v___y_5014_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 2, v_v_5002_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 1, v_k_5001_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 0, v___x_5012_);
                    v___x_5021_ = v___x_4997_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_k_5001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_v_5002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 3, v___y_5014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 4, v___x_5019_);
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
                crate::leanh::lean_dec(v___y_5026_);
                crate::leanh::lean_dec(v___x_5024_);
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v_l_5003_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v_l_4986_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_4985_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_4984_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5027_);
                    v___x_5029_ = v___x_4977_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5033_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 0, v___x_5027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 1, v_k_4984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 2, v_v_4985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 3, v_l_4986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5033_, 4, v_l_5003_);
                    v___x_5029_ = v_reuseFailAlloc_5033_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_5030_ = lean_nat_add(v___x_4981_, v_size_4982_);
                if crate::leanh::lean_obj_tag(v_r_5004_) == 0 {
                    v_size_5031_ = crate::leanh::lean_ctor_get(v_r_5004_, 0);
                    crate::leanh::lean_inc(v_size_5031_);
                    v___y_5014_ = v___x_5029_;
                    v___y_5015_ = v___x_5030_;
                    v___y_5016_ = v_size_5031_;
                    state = 5;
                    continue;
                } else {
                    v___x_5032_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5014_ = v___x_5029_;
                    v___y_5015_ = v___x_5030_;
                    v___y_5016_ = v___x_5032_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_5054_ = (!crate::leanh::lean_is_exclusive(v_r_4975_)) as u8;
                if v_isSharedCheck_5054_ == 0 {
                    v_unused_5055_ = crate::leanh::lean_ctor_get(v_r_4975_, 4);
                    crate::leanh::lean_dec(v_unused_5055_);
                    v_unused_5056_ = crate::leanh::lean_ctor_get(v_r_4975_, 3);
                    crate::leanh::lean_dec(v_unused_5056_);
                    v_unused_5057_ = crate::leanh::lean_ctor_get(v_r_4975_, 2);
                    crate::leanh::lean_dec(v_unused_5057_);
                    v_unused_5058_ = crate::leanh::lean_ctor_get(v_r_4975_, 1);
                    crate::leanh::lean_dec(v_unused_5058_);
                    v_unused_5059_ = crate::leanh::lean_ctor_get(v_r_4975_, 0);
                    crate::leanh::lean_dec(v_unused_5059_);
                    v___x_5049_ = v_r_4975_;
                    v_isShared_5050_ = v_isSharedCheck_5054_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_4975_);
                    v___x_5049_ = crate::leanh::lean_box(0);
                    v_isShared_5050_ = v_isSharedCheck_5054_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5050_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5049_, 4, v___x_5047_);
                    crate::leanh::lean_ctor_set(v___x_5049_, 3, v_l_4986_);
                    crate::leanh::lean_ctor_set(v___x_5049_, 2, v_v_4985_);
                    crate::leanh::lean_ctor_set(v___x_5049_, 1, v_k_4984_);
                    crate::leanh::lean_ctor_set(v___x_5049_, 0, v___x_5043_);
                    v___x_5052_ = v___x_5049_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5053_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 1, v_k_4984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 2, v_v_4985_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 3, v_l_4986_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5053_, 4, v___x_5047_);
                    v___x_5052_ = v_reuseFailAlloc_5053_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5052_;
            }
            13 => {
                v___x_5074_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_5068_);
                if v_isShared_5073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5072_, 3, v_r_5068_);
                    crate::leanh::lean_ctor_set(v___x_5072_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v___x_5072_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v___x_5072_, 0, v___x_4981_);
                    v___x_5076_ = v___x_5072_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5080_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 0, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 3, v_r_5068_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5080_, 4, v_r_5068_);
                    v___x_5076_ = v_reuseFailAlloc_5080_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v___x_5076_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v_l_5067_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_5070_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_5069_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5074_);
                    v___x_5078_ = v___x_4977_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5079_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 0, v___x_5074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 1, v_k_5069_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 2, v_v_5070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 3, v_l_5067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5079_, 4, v___x_5076_);
                    v___x_5078_ = v_reuseFailAlloc_5079_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5078_;
            }
            16 => {
                v_k_5090_ = crate::leanh::lean_ctor_get(v_r_5084_, 1);
                v_v_5091_ = crate::leanh::lean_ctor_get(v_r_5084_, 2);
                v_isSharedCheck_5105_ = (!crate::leanh::lean_is_exclusive(v_r_5084_)) as u8;
                if v_isSharedCheck_5105_ == 0 {
                    v_unused_5106_ = crate::leanh::lean_ctor_get(v_r_5084_, 4);
                    crate::leanh::lean_dec(v_unused_5106_);
                    v_unused_5107_ = crate::leanh::lean_ctor_get(v_r_5084_, 3);
                    crate::leanh::lean_dec(v_unused_5107_);
                    v_unused_5108_ = crate::leanh::lean_ctor_get(v_r_5084_, 0);
                    crate::leanh::lean_dec(v_unused_5108_);
                    v___x_5093_ = v_r_5084_;
                    v_isShared_5094_ = v_isSharedCheck_5105_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_5091_);
                    crate::leanh::lean_inc(v_k_5090_);
                    crate::leanh::lean_dec(v_r_5084_);
                    v___x_5093_ = crate::leanh::lean_box(0);
                    v_isShared_5094_ = v_isSharedCheck_5105_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_5095_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_5094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5093_, 4, v_l_5067_);
                    crate::leanh::lean_ctor_set(v___x_5093_, 3, v_l_5067_);
                    crate::leanh::lean_ctor_set(v___x_5093_, 2, v_v_5086_);
                    crate::leanh::lean_ctor_set(v___x_5093_, 1, v_k_5085_);
                    crate::leanh::lean_ctor_set(v___x_5093_, 0, v___x_4981_);
                    v___x_5097_ = v___x_5093_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5104_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 1, v_k_5085_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 2, v_v_5086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 3, v_l_5067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5104_, 4, v_l_5067_);
                    v___x_5097_ = v_reuseFailAlloc_5104_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_5089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5088_, 4, v_l_5067_);
                    crate::leanh::lean_ctor_set(v___x_5088_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v___x_5088_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v___x_5088_, 0, v___x_4981_);
                    v___x_5099_ = v___x_5088_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5103_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 0, v___x_4981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_l_5067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5103_, 4, v_l_5067_);
                    v___x_5099_ = v_reuseFailAlloc_5103_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v___x_5099_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v___x_5097_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_5091_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_5090_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5095_);
                    v___x_5101_ = v___x_4977_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5102_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 1, v_k_5090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 2, v_v_5091_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 3, v___x_5097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5102_, 4, v___x_5099_);
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
                v_size_5139_ = crate::leanh::lean_ctor_get(v_l_5126_, 0);
                v_k_5140_ = crate::leanh::lean_ctor_get(v_l_5126_, 1);
                v_v_5141_ = crate::leanh::lean_ctor_get(v_l_5126_, 2);
                v_l_5142_ = crate::leanh::lean_ctor_get(v_l_5126_, 3);
                v_r_5143_ = crate::leanh::lean_ctor_get(v_l_5126_, 4);
                v_size_5144_ = crate::leanh::lean_ctor_get(v_r_5127_, 0);
                v___x_5145_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5146_ = lean_nat_mul(v___x_5145_, v_size_5144_);
                v___x_5147_ = lean_nat_dec_lt(v_size_5139_, v___x_5146_);
                crate::leanh::lean_dec(v___x_5146_);
                if v___x_5147_ == 0 {
                    crate::leanh::lean_inc(v_r_5143_);
                    crate::leanh::lean_inc(v_l_5142_);
                    crate::leanh::lean_inc(v_v_5141_);
                    crate::leanh::lean_inc(v_k_5140_);
                    v_isSharedCheck_5175_ = (!crate::leanh::lean_is_exclusive(v_l_5126_)) as u8;
                    if v_isSharedCheck_5175_ == 0 {
                        v_unused_5176_ = crate::leanh::lean_ctor_get(v_l_5126_, 4);
                        crate::leanh::lean_dec(v_unused_5176_);
                        v_unused_5177_ = crate::leanh::lean_ctor_get(v_l_5126_, 3);
                        crate::leanh::lean_dec(v_unused_5177_);
                        v_unused_5178_ = crate::leanh::lean_ctor_get(v_l_5126_, 2);
                        crate::leanh::lean_dec(v_unused_5178_);
                        v_unused_5179_ = crate::leanh::lean_ctor_get(v_l_5126_, 1);
                        crate::leanh::lean_dec(v_unused_5179_);
                        v_unused_5180_ = crate::leanh::lean_ctor_get(v_l_5126_, 0);
                        crate::leanh::lean_dec(v_unused_5180_);
                        v___x_5149_ = v_l_5126_;
                        v_isShared_5150_ = v_isSharedCheck_5175_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_5126_);
                        v___x_5149_ = crate::leanh::lean_box(0);
                        v_isShared_5150_ = v_isSharedCheck_5175_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4977_);
                    v___x_5181_ = lean_nat_add(v___x_5121_, v_size_5122_);
                    v___x_5182_ = lean_nat_add(v___x_5181_, v_size_5123_);
                    crate::leanh::lean_dec(v_size_5123_);
                    v___x_5183_ = lean_nat_add(v___x_5181_, v_size_5139_);
                    crate::leanh::lean_dec(v___x_5181_);
                    crate::leanh::lean_inc_ref(v_l_4974_);
                    if v_isShared_5138_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5137_, 4, v_l_5126_);
                        crate::leanh::lean_ctor_set(v___x_5137_, 3, v_l_4974_);
                        crate::leanh::lean_ctor_set(v___x_5137_, 2, v_v_4973_);
                        crate::leanh::lean_ctor_set(v___x_5137_, 1, v_k_4972_);
                        crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5183_);
                        v___x_5185_ = v___x_5137_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_5198_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 0, v___x_5183_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 1, v_k_4972_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 2, v_v_4973_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 3, v_l_4974_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5198_, 4, v_l_5126_);
                        v___x_5185_ = v_reuseFailAlloc_5198_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_5151_ = lean_nat_add(v___x_5121_, v_size_5122_);
                v___x_5152_ = lean_nat_add(v___x_5151_, v_size_5123_);
                crate::leanh::lean_dec(v_size_5123_);
                if crate::leanh::lean_obj_tag(v_l_5142_) == 0 {
                    v_size_5173_ = crate::leanh::lean_ctor_get(v_l_5142_, 0);
                    crate::leanh::lean_inc(v_size_5173_);
                    v___y_5165_ = v_size_5173_;
                    state = 29;
                    continue;
                } else {
                    v___x_5174_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5165_ = v___x_5174_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_5157_ = lean_nat_add(v___y_5154_, v___y_5156_);
                crate::leanh::lean_dec(v___y_5156_);
                crate::leanh::lean_dec(v___y_5154_);
                if v_isShared_5150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5149_, 4, v_r_5127_);
                    crate::leanh::lean_ctor_set(v___x_5149_, 3, v_r_5143_);
                    crate::leanh::lean_ctor_set(v___x_5149_, 2, v_v_5125_);
                    crate::leanh::lean_ctor_set(v___x_5149_, 1, v_k_5124_);
                    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5157_);
                    v___x_5159_ = v___x_5149_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5163_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 0, v___x_5157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 1, v_k_5124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 2, v_v_5125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 3, v_r_5143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5163_, 4, v_r_5127_);
                    v___x_5159_ = v_reuseFailAlloc_5163_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_5138_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5137_, 4, v___x_5159_);
                    crate::leanh::lean_ctor_set(v___x_5137_, 3, v___y_5155_);
                    crate::leanh::lean_ctor_set(v___x_5137_, 2, v_v_5141_);
                    crate::leanh::lean_ctor_set(v___x_5137_, 1, v_k_5140_);
                    crate::leanh::lean_ctor_set(v___x_5137_, 0, v___x_5152_);
                    v___x_5161_ = v___x_5137_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5162_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_k_5140_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 2, v_v_5141_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 3, v___y_5155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5162_, 4, v___x_5159_);
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
                crate::leanh::lean_dec(v___y_5165_);
                crate::leanh::lean_dec(v___x_5151_);
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v_l_5142_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5166_);
                    v___x_5168_ = v___x_4977_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5172_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v___x_5166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 3, v_l_4974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 4, v_l_5142_);
                    v___x_5168_ = v_reuseFailAlloc_5172_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_5169_ = lean_nat_add(v___x_5121_, v_size_5144_);
                if crate::leanh::lean_obj_tag(v_r_5143_) == 0 {
                    v_size_5170_ = crate::leanh::lean_ctor_get(v_r_5143_, 0);
                    crate::leanh::lean_inc(v_size_5170_);
                    v___y_5154_ = v___x_5169_;
                    v___y_5155_ = v___x_5168_;
                    v___y_5156_ = v_size_5170_;
                    state = 26;
                    continue;
                } else {
                    v___x_5171_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5154_ = v___x_5169_;
                    v___y_5155_ = v___x_5168_;
                    v___y_5156_ = v___x_5171_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_5192_ = (!crate::leanh::lean_is_exclusive(v_l_4974_)) as u8;
                if v_isSharedCheck_5192_ == 0 {
                    v_unused_5193_ = crate::leanh::lean_ctor_get(v_l_4974_, 4);
                    crate::leanh::lean_dec(v_unused_5193_);
                    v_unused_5194_ = crate::leanh::lean_ctor_get(v_l_4974_, 3);
                    crate::leanh::lean_dec(v_unused_5194_);
                    v_unused_5195_ = crate::leanh::lean_ctor_get(v_l_4974_, 2);
                    crate::leanh::lean_dec(v_unused_5195_);
                    v_unused_5196_ = crate::leanh::lean_ctor_get(v_l_4974_, 1);
                    crate::leanh::lean_dec(v_unused_5196_);
                    v_unused_5197_ = crate::leanh::lean_ctor_get(v_l_4974_, 0);
                    crate::leanh::lean_dec(v_unused_5197_);
                    v___x_5187_ = v_l_4974_;
                    v_isShared_5188_ = v_isSharedCheck_5192_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_4974_);
                    v___x_5187_ = crate::leanh::lean_box(0);
                    v_isShared_5188_ = v_isSharedCheck_5192_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_5188_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5187_, 4, v_r_5127_);
                    crate::leanh::lean_ctor_set(v___x_5187_, 3, v___x_5185_);
                    crate::leanh::lean_ctor_set(v___x_5187_, 2, v_v_5125_);
                    crate::leanh::lean_ctor_set(v___x_5187_, 1, v_k_5124_);
                    crate::leanh::lean_ctor_set(v___x_5187_, 0, v___x_5182_);
                    v___x_5190_ = v___x_5187_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5191_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 0, v___x_5182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_k_5124_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 2, v_v_5125_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 3, v___x_5185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5191_, 4, v_r_5127_);
                    v___x_5190_ = v_reuseFailAlloc_5191_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5190_;
            }
            34 => {
                v_k_5212_ = crate::leanh::lean_ctor_get(v_l_5205_, 1);
                v_v_5213_ = crate::leanh::lean_ctor_get(v_l_5205_, 2);
                v_isSharedCheck_5227_ = (!crate::leanh::lean_is_exclusive(v_l_5205_)) as u8;
                if v_isSharedCheck_5227_ == 0 {
                    v_unused_5228_ = crate::leanh::lean_ctor_get(v_l_5205_, 4);
                    crate::leanh::lean_dec(v_unused_5228_);
                    v_unused_5229_ = crate::leanh::lean_ctor_get(v_l_5205_, 3);
                    crate::leanh::lean_dec(v_unused_5229_);
                    v_unused_5230_ = crate::leanh::lean_ctor_get(v_l_5205_, 0);
                    crate::leanh::lean_dec(v_unused_5230_);
                    v___x_5215_ = v_l_5205_;
                    v_isShared_5216_ = v_isSharedCheck_5227_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_5213_);
                    crate::leanh::lean_inc(v_k_5212_);
                    crate::leanh::lean_dec(v_l_5205_);
                    v___x_5215_ = crate::leanh::lean_box(0);
                    v_isShared_5216_ = v_isSharedCheck_5227_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_5217_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_5206_, 2);
                if v_isShared_5216_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5215_, 4, v_r_5206_);
                    crate::leanh::lean_ctor_set(v___x_5215_, 3, v_r_5206_);
                    crate::leanh::lean_ctor_set(v___x_5215_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v___x_5215_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v___x_5215_, 0, v___x_5121_);
                    v___x_5219_ = v___x_5215_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5226_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 3, v_r_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5226_, 4, v_r_5206_);
                    v___x_5219_ = v_reuseFailAlloc_5226_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_5206_);
                if v_isShared_5211_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5210_, 3, v_r_5206_);
                    crate::leanh::lean_ctor_set(v___x_5210_, 0, v___x_5121_);
                    v___x_5221_ = v___x_5210_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5225_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 0, v___x_5121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 1, v_k_5207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 2, v_v_5208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 3, v_r_5206_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5225_, 4, v_r_5206_);
                    v___x_5221_ = v_reuseFailAlloc_5225_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v___x_5221_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v___x_5219_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_5213_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_5212_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5217_);
                    v___x_5223_ = v___x_4977_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 0, v___x_5217_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 1, v_k_5212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 2, v_v_5213_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 3, v___x_5219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 4, v___x_5221_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5223_;
            }
            39 => {
                v___x_5240_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_5239_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5238_, 4, v_l_5205_);
                    crate::leanh::lean_ctor_set(v___x_5238_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v___x_5238_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v___x_5238_, 0, v___x_5121_);
                    v___x_5242_ = v___x_5238_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5246_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 0, v___x_5121_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 1, v_k_4972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 2, v_v_4973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 3, v_l_5205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5246_, 4, v_l_5205_);
                    v___x_5242_ = v_reuseFailAlloc_5246_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_4978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4977_, 4, v_r_5234_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 3, v___x_5242_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 2, v_v_5236_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 1, v_k_5235_);
                    crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_5240_);
                    v___x_5244_ = v___x_4977_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5245_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 1, v_k_5235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 2, v_v_5236_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 3, v___x_5242_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 4, v_r_5234_);
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
    mut v_k_5258_: *mut crate::leanh::LeanObject,
    mut v_t_5259_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_5259_) == 0 {
                    v_k_5260_ = crate::leanh::lean_ctor_get(v_t_5259_, 1);
                    v_l_5261_ = crate::leanh::lean_ctor_get(v_t_5259_, 3);
                    v_r_5262_ = crate::leanh::lean_ctor_get(v_t_5259_, 4);
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
    mut v_k_5268_: *mut crate::leanh::LeanObject,
    mut v_t_5269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5270_: u8 = 0;
    let mut v_r_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5270_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(
            v_k_5268_, v_t_5269_,
        );
    crate::leanh::lean_dec(v_t_5269_);
    crate::leanh::lean_dec(v_k_5268_);
    v_r_5271_ = crate::leanh::lean_box((v_res_5270_) as usize);
    return v_r_5271_;
}
pub unsafe fn l_Lean_Level_collectMVars(
    mut v_u_5272_: *mut crate::leanh::LeanObject,
    mut v_s_5273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: u8 = 0;
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_u_5272_) {
                1 => {
                    v_a_5279_ = crate::leanh::lean_ctor_get(v_u_5272_, 0);
                    crate::leanh::lean_inc(v_a_5279_);
                    crate::leanh::lean_dec_ref_known(v_u_5272_, 1);
                    v_u_5272_ = v_a_5279_;
                    state = 0;
                    continue;
                }
                2 => {
                    v_a_5281_ = crate::leanh::lean_ctor_get(v_u_5272_, 0);
                    crate::leanh::lean_inc(v_a_5281_);
                    v_a_5282_ = crate::leanh::lean_ctor_get(v_u_5272_, 1);
                    crate::leanh::lean_inc(v_a_5282_);
                    crate::leanh::lean_dec_ref_known(v_u_5272_, 2);
                    v_u_5275_ = v_a_5281_;
                    v_v_5276_ = v_a_5282_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_5283_ = crate::leanh::lean_ctor_get(v_u_5272_, 0);
                    crate::leanh::lean_inc(v_a_5283_);
                    v_a_5284_ = crate::leanh::lean_ctor_get(v_u_5272_, 1);
                    crate::leanh::lean_inc(v_a_5284_);
                    crate::leanh::lean_dec_ref_known(v_u_5272_, 2);
                    v_u_5275_ = v_a_5283_;
                    v_v_5276_ = v_a_5284_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_a_5285_ = crate::leanh::lean_ctor_get(v_u_5272_, 0);
                    crate::leanh::lean_inc(v_a_5285_);
                    crate::leanh::lean_dec_ref_known(v_u_5272_, 1);
                    v___x_5286_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(v_a_5285_, v_s_5273_);
                    if v___x_5286_ == 0 {
                        v___x_5287_ = crate::leanh::lean_box(0);
                        v___x_5288_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(v_a_5285_, v___x_5287_, v_s_5273_);
                        return v___x_5288_;
                    } else {
                        crate::leanh::lean_dec(v_a_5285_);
                        return v_s_5273_;
                    }
                }
                _ => {
                    crate::leanh::lean_dec(v_u_5272_);
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
    mut v_00_u03b2_5289_: *mut crate::leanh::LeanObject,
    mut v_k_5290_: *mut crate::leanh::LeanObject,
    mut v_t_5291_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5292_: u8 = 0;
    v___x_5292_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___redArg(
            v_k_5290_, v_t_5291_,
        );
    return v___x_5292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0___boxed(
    mut v_00_u03b2_5293_: *mut crate::leanh::LeanObject,
    mut v_k_5294_: *mut crate::leanh::LeanObject,
    mut v_t_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5296_: u8 = 0;
    let mut v_r_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_collectMVars_spec__0(
        v_00_u03b2_5293_,
        v_k_5294_,
        v_t_5295_,
    );
    crate::leanh::lean_dec(v_t_5295_);
    crate::leanh::lean_dec(v_k_5294_);
    v_r_5297_ = crate::leanh::lean_box((v_res_5296_) as usize);
    return v_r_5297_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1(
    mut v_00_u03b2_5298_: *mut crate::leanh::LeanObject,
    mut v_k_5299_: *mut crate::leanh::LeanObject,
    mut v_v_5300_: *mut crate::leanh::LeanObject,
    mut v_t_5301_: *mut crate::leanh::LeanObject,
    mut v_hl_5302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5303_ =
        l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_collectMVars_spec__1___redArg(
            v_k_5299_, v_v_5300_, v_t_5301_,
        );
    return v___x_5303_;
}
pub unsafe fn l___private_Lean_Level_0__Lean_Level_find_x3f_visit(
    mut v_p_5304_: *mut crate::leanh::LeanObject,
    mut v_u_5305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_u_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: u8 = 0;
    let mut v_a_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_p_5304_);
                crate::leanh::lean_inc(v_u_5305_);
                v___x_5311_ = crate::leanh::lean_apply_1(v_p_5304_, v_u_5305_);
                v___x_5312_ = (crate::leanh::lean_unbox(v___x_5311_) as u8);
                if v___x_5312_ == 0 {
                    match crate::leanh::lean_obj_tag(v_u_5305_) {
                        1 => {
                            v_a_5313_ = crate::leanh::lean_ctor_get(v_u_5305_, 0);
                            crate::leanh::lean_inc(v_a_5313_);
                            crate::leanh::lean_dec_ref_known(v_u_5305_, 1);
                            v_u_5305_ = v_a_5313_;
                            state = 0;
                            continue;
                        }
                        2 => {
                            v_a_5315_ = crate::leanh::lean_ctor_get(v_u_5305_, 0);
                            crate::leanh::lean_inc(v_a_5315_);
                            v_a_5316_ = crate::leanh::lean_ctor_get(v_u_5305_, 1);
                            crate::leanh::lean_inc(v_a_5316_);
                            crate::leanh::lean_dec_ref_known(v_u_5305_, 2);
                            v_u_5307_ = v_a_5315_;
                            v_v_5308_ = v_a_5316_;
                            state = 1;
                            continue;
                        }
                        3 => {
                            v_a_5317_ = crate::leanh::lean_ctor_get(v_u_5305_, 0);
                            crate::leanh::lean_inc(v_a_5317_);
                            v_a_5318_ = crate::leanh::lean_ctor_get(v_u_5305_, 1);
                            crate::leanh::lean_inc(v_a_5318_);
                            crate::leanh::lean_dec_ref_known(v_u_5305_, 2);
                            v_u_5307_ = v_a_5317_;
                            v_v_5308_ = v_a_5318_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            crate::leanh::lean_dec(v_u_5305_);
                            crate::leanh::lean_dec_ref(v_p_5304_);
                            v___x_5319_ = crate::leanh::lean_box(0);
                            return v___x_5319_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_p_5304_);
                    v___x_5320_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5320_, 0, v_u_5305_);
                    return v___x_5320_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_p_5304_);
                v___x_5309_ =
                    l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5304_, v_u_5307_);
                if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                    v_u_5305_ = v_v_5308_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_v_5308_);
                    crate::leanh::lean_dec_ref(v_p_5304_);
                    return v___x_5309_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Level_find_x3f(
    mut v_u_5321_: *mut crate::leanh::LeanObject,
    mut v_p_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5323_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5322_, v_u_5321_);
    return v___x_5323_;
}
pub unsafe fn l_Lean_Level_any(
    mut v_u_5324_: *mut crate::leanh::LeanObject,
    mut v_p_5325_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5326_ = l___private_Lean_Level_0__Lean_Level_find_x3f_visit(v_p_5325_, v_u_5324_);
    if crate::leanh::lean_obj_tag(v___x_5326_) == 0 {
        let mut v___x_5327_: u8 = 0;
        v___x_5327_ = 0;
        return v___x_5327_;
    } else {
        let mut v___x_5328_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v___x_5326_, 1);
        v___x_5328_ = 1;
        return v___x_5328_;
    }
}
pub unsafe fn l_Lean_Level_any___boxed(
    mut v_u_5329_: *mut crate::leanh::LeanObject,
    mut v_p_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5331_: u8 = 0;
    let mut v_r_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5331_ = l_Lean_Level_any(v_u_5329_, v_p_5330_);
    v_r_5332_ = crate::leanh::lean_box((v_res_5331_) as usize);
    return v_r_5332_;
}
pub unsafe fn l_Nat_toLevel(
    mut v_n_5333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5334_ = l_Lean_Level_ofNat(v_n_5333_);
    return v___x_5334_;
}
pub unsafe fn l_Nat_toLevel___boxed(
    mut v_n_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5336_ = l_Nat_toLevel(v_n_5335_);
    crate::leanh::lean_dec(v_n_5335_);
    return v_res_5336_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_QSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Hygiene(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_instInhabitedData___aux__1 = _init_l_Lean_instInhabitedData___aux__1();
    l_Lean_instInhabitedData = _init_l_Lean_instInhabitedData();
    l_Lean_instInhabitedLevelMVarId_default = _init_l_Lean_instInhabitedLevelMVarId_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLevelMVarId_default);
    l_Lean_instInhabitedLevelMVarId = _init_l_Lean_instInhabitedLevelMVarId();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLevelMVarId);
    l_Lean_instInhabitedLMVarIdSet___aux__1 = _init_l_Lean_instInhabitedLMVarIdSet___aux__1();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet___aux__1);
    l_Lean_instInhabitedLMVarIdSet = _init_l_Lean_instInhabitedLMVarIdSet();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLMVarIdSet);
    l_Lean_instEmptyCollectionLMVarIdSet___aux__1 =
        _init_l_Lean_instEmptyCollectionLMVarIdSet___aux__1();
    crate::leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet___aux__1);
    l_Lean_instEmptyCollectionLMVarIdSet = _init_l_Lean_instEmptyCollectionLMVarIdSet();
    crate::leanh::lean_mark_persistent(l_Lean_instEmptyCollectionLMVarIdSet);
    l_Lean_Level_zero___override = _init_l_Lean_Level_zero___override();
    crate::leanh::lean_mark_persistent(l_Lean_Level_zero___override);
    l_Lean_instInhabitedLevel_default = _init_l_Lean_instInhabitedLevel_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLevel_default);
    l_Lean_instInhabitedLevel = _init_l_Lean_instInhabitedLevel();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedLevel);
    l_Lean_levelZero = _init_l_Lean_levelZero();
    crate::leanh::lean_mark_persistent(l_Lean_levelZero);
    l_Lean_Level_one = _init_l_Lean_Level_one();
    crate::leanh::lean_mark_persistent(l_Lean_Level_one);
    l_Lean_levelOne = _init_l_Lean_levelOne();
    crate::leanh::lean_mark_persistent(l_Lean_levelOne);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Level(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_QSort(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashSet(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Hygiene(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Coe(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Level(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Level(builtin);
}
