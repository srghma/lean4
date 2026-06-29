// Lean compiler output
// Module: Lake.Build.Key
// Imports: Init.Data.Order Lake.Util.Name Init.Data.String.Search Init.Data.Iterators.Consumers
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Data::Order::{
    initialize_Init_Data_Order, runtime_initialize_Init_Data_Order,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lake::Util::Name::{
    initialize_Lake_Util_Name, l_Lake_Name_eraseHead, l_Lake_stringToLegalOrSimpleName,
    runtime_initialize_Lake_Util_Name,
};
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_getPrefix,
    l_Lean_Name_isAnonymous,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_sub, lean_panic_fn_borrowed, lean_string_utf8_byte_size,
    lean_uint32_dec_eq, lean_uint64_mix_hash, lean_uint64_of_nat,
};
pub static l_Lake_instInhabitedBuildKey_default___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_instInhabitedBuildKey_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedBuildKey_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instInhabitedBuildKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 109, 111, 100, 117,
            108, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__2_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_instReprBuildKey_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildKey_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprBuildKey_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildKey_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildKey_repr___closed__5_value: crate::leanh::LeanStringObject<22> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97,
            103, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__7_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__8_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97,
            103, 101, 77, 111, 100, 117, 108, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__9_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__10_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__9_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__11_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97,
            103, 101, 84, 97, 114, 103, 101, 116, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__12_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__11_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__13_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__12_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__14_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 102, 97, 99, 101, 116,
            0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__15_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__14_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__16_value: crate::leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__15_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_instReprBuildKey___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprBuildKey_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBuildKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instReprBuildKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_instHashableBuildKey_hash___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__0: u64 = 0;
static mut l_Lake_instHashableBuildKey_hash___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__1: u64 = 0;
static mut l_Lake_instHashableBuildKey_hash___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__2: u64 = 0;
pub static l_Lake_instHashableBuildKey___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instHashableBuildKey_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instHashableBuildKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableBuildKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_instHashableBuildKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableBuildKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value:
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
    m_fun: l_Lake_PartialBuildKey_mk___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instCoeBuildKey___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instCoeBuildKey: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value:
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
    m_fun: l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instRepr___private__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instRepr___private__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instInhabited___closed__0_value: crate::leanh::LeanCtorObject<1> =
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
static mut l_Lake_PartialBuildKey_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value: crate::leanh::LeanStringObject<83> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 100, 101, 102, 97, 117, 108, 116, 32, 112, 97, 99, 107, 97, 103, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 105, 110, 32, 112, 97, 114, 116, 105, 97, 108, 32, 98, 117, 105, 108, 100, 32, 107, 101, 121, 115, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 39, 47, 39, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value: crate::leanh::LeanStringObject<50> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 32, 110, 97, 109, 101, 32, 97, 102, 116, 101, 114, 32, 39, 43, 39, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32,
        101, 109, 112, 116, 121, 32, 102, 97, 99, 101, 116, 0,
    ],
};
static mut l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__0_value: crate::leanh::LeanArrayObject<0> =
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
static mut l_Lake_PartialBuildKey_parse___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__1_value: crate::leanh::LeanStringObject<15> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 46, 75, 101, 121, 0,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__2_value: crate::leanh::LeanStringObject<27> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 97, 107, 101, 46, 80, 97, 114, 116, 105, 97, 108, 66, 117, 105, 108, 100, 75, 101,
            121, 46, 112, 97, 114, 115, 101, 0,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__3_value: crate::leanh::LeanStringObject<34> =
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
static mut l_Lake_PartialBuildKey_parse___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_PartialBuildKey_parse___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PartialBuildKey_parse___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_PartialBuildKey_parse___closed__5_value: crate::leanh::LeanStringObject<32> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58,
            32, 101, 109, 112, 116, 121, 32, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__0_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [47, 43, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [47, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instToString___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_PartialBuildKey_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_BuildKey_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildKey_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildKey_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildKey_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_BuildKey_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildKey_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_BuildKey_ctorIdx(
    mut v_x_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1011_) {
        0 => {
            let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1012_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1012_;
        }
        1 => {
            let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1013_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1013_;
        }
        2 => {
            let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1014_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1014_;
        }
        3 => {
            let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1015_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1015_;
        }
        _ => {
            let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1016_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1016_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_ctorIdx___boxed(
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Lake_BuildKey_ctorIdx(v_x_1017_);
    crate::leanh::lean_dec_ref(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Lake_BuildKey_ctorElim___redArg(
    mut v_t_1019_: *mut crate::leanh::LeanObject,
    mut v_k_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_1019_) {
        2 => {
            let mut v_package_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_package_1021_ = crate::leanh::lean_ctor_get(v_t_1019_, 0);
            crate::leanh::lean_inc(v_package_1021_);
            v_module_1022_ = crate::leanh::lean_ctor_get(v_t_1019_, 1);
            crate::leanh::lean_inc(v_module_1022_);
            crate::leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1023_ = crate::leanh::lean_apply_2(v_k_1020_, v_package_1021_, v_module_1022_);
            return v___x_1023_;
        }
        3 => {
            let mut v_package_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_package_1024_ = crate::leanh::lean_ctor_get(v_t_1019_, 0);
            crate::leanh::lean_inc(v_package_1024_);
            v_target_1025_ = crate::leanh::lean_ctor_get(v_t_1019_, 1);
            crate::leanh::lean_inc(v_target_1025_);
            crate::leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1026_ = crate::leanh::lean_apply_2(v_k_1020_, v_package_1024_, v_target_1025_);
            return v___x_1026_;
        }
        4 => {
            let mut v_target_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_target_1027_ = crate::leanh::lean_ctor_get(v_t_1019_, 0);
            crate::leanh::lean_inc_ref(v_target_1027_);
            v_facet_1028_ = crate::leanh::lean_ctor_get(v_t_1019_, 1);
            crate::leanh::lean_inc(v_facet_1028_);
            crate::leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1029_ = crate::leanh::lean_apply_2(v_k_1020_, v_target_1027_, v_facet_1028_);
            return v___x_1029_;
        }
        _ => {
            let mut v_module_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_module_1030_ = crate::leanh::lean_ctor_get(v_t_1019_, 0);
            crate::leanh::lean_inc(v_module_1030_);
            crate::leanh::lean_dec_ref(v_t_1019_);
            v___x_1031_ = crate::leanh::lean_apply_1(v_k_1020_, v_module_1030_);
            return v___x_1031_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_ctorElim(
    mut v_motive_1032_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1033_: *mut crate::leanh::LeanObject,
    mut v_t_1034_: *mut crate::leanh::LeanObject,
    mut v_h_1035_: *mut crate::leanh::LeanObject,
    mut v_k_1036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1034_, v_k_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Lake_BuildKey_ctorElim___boxed(
    mut v_motive_1038_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1039_: *mut crate::leanh::LeanObject,
    mut v_t_1040_: *mut crate::leanh::LeanObject,
    mut v_h_1041_: *mut crate::leanh::LeanObject,
    mut v_k_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1043_ = l_Lake_BuildKey_ctorElim(
        v_motive_1038_,
        v_ctorIdx_1039_,
        v_t_1040_,
        v_h_1041_,
        v_k_1042_,
    );
    crate::leanh::lean_dec(v_ctorIdx_1039_);
    return v_res_1043_;
}
pub unsafe fn l_Lake_BuildKey_module_elim___redArg(
    mut v_t_1044_: *mut crate::leanh::LeanObject,
    mut v_module_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1044_, v_module_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Lake_BuildKey_module_elim(
    mut v_motive_1047_: *mut crate::leanh::LeanObject,
    mut v_t_1048_: *mut crate::leanh::LeanObject,
    mut v_h_1049_: *mut crate::leanh::LeanObject,
    mut v_module_1050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1048_, v_module_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Lake_BuildKey_package_elim___redArg(
    mut v_t_1052_: *mut crate::leanh::LeanObject,
    mut v_package_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1052_, v_package_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Lake_BuildKey_package_elim(
    mut v_motive_1055_: *mut crate::leanh::LeanObject,
    mut v_t_1056_: *mut crate::leanh::LeanObject,
    mut v_h_1057_: *mut crate::leanh::LeanObject,
    mut v_package_1058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1056_, v_package_1058_);
    return v___x_1059_;
}
pub unsafe fn l_Lake_BuildKey_packageModule_elim___redArg(
    mut v_t_1060_: *mut crate::leanh::LeanObject,
    mut v_packageModule_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1060_, v_packageModule_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lake_BuildKey_packageModule_elim(
    mut v_motive_1063_: *mut crate::leanh::LeanObject,
    mut v_t_1064_: *mut crate::leanh::LeanObject,
    mut v_h_1065_: *mut crate::leanh::LeanObject,
    mut v_packageModule_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1064_, v_packageModule_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lake_BuildKey_packageTarget_elim___redArg(
    mut v_t_1068_: *mut crate::leanh::LeanObject,
    mut v_packageTarget_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1068_, v_packageTarget_1069_);
    return v___x_1070_;
}
pub unsafe fn l_Lake_BuildKey_packageTarget_elim(
    mut v_motive_1071_: *mut crate::leanh::LeanObject,
    mut v_t_1072_: *mut crate::leanh::LeanObject,
    mut v_h_1073_: *mut crate::leanh::LeanObject,
    mut v_packageTarget_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1072_, v_packageTarget_1074_);
    return v___x_1075_;
}
pub unsafe fn l_Lake_BuildKey_facet_elim___redArg(
    mut v_t_1076_: *mut crate::leanh::LeanObject,
    mut v_facet_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1076_, v_facet_1077_);
    return v___x_1078_;
}
pub unsafe fn l_Lake_BuildKey_facet_elim(
    mut v_motive_1079_: *mut crate::leanh::LeanObject,
    mut v_t_1080_: *mut crate::leanh::LeanObject,
    mut v_h_1081_: *mut crate::leanh::LeanObject,
    mut v_facet_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1080_, v_facet_1082_);
    return v___x_1083_;
}
pub unsafe fn _init_l_Lake_instReprBuildKey_repr___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1095_ = lean_nat_to_int(v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn _init_l_Lake_instReprBuildKey_repr___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1096_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1097_ = lean_nat_to_int(v___x_1096_);
    return v___x_1097_;
}
pub unsafe fn l_Lake_instReprBuildKey_repr(
    mut v_x_1122_: *mut crate::leanh::LeanObject,
    mut v_prec_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_module_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: u8 = 0;
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1158_: u8 = 0;
    let mut v___y_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_package_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___y_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_target_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u8 = 0;
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1122_) {
                0 => {
                    v_module_1124_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    crate::leanh::lean_inc(v_module_1124_);
                    crate::leanh::lean_dec_ref_known(v_x_1122_, 1);
                    v___x_1135_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1136_ = lean_nat_dec_le(v___x_1135_, v_prec_1123_);
                    if v___x_1136_ == 0 {
                        v___x_1137_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__3,
                        );
                        v___y_1126_ = v___x_1137_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1138_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__4,
                        );
                        v___y_1126_ = v___x_1138_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_package_1139_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    crate::leanh::lean_inc(v_package_1139_);
                    crate::leanh::lean_dec_ref_known(v_x_1122_, 1);
                    v___x_1150_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1151_ = lean_nat_dec_le(v___x_1150_, v_prec_1123_);
                    if v___x_1151_ == 0 {
                        v___x_1152_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__3,
                        );
                        v___y_1141_ = v___x_1152_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1153_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__4,
                        );
                        v___y_1141_ = v___x_1153_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_package_1154_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    v_module_1155_ = crate::leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1179_ = (!crate::leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1179_ == 0 {
                        v___x_1157_ = v_x_1122_;
                        v_isShared_1158_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_module_1155_);
                        crate::leanh::lean_inc(v_package_1154_);
                        crate::leanh::lean_dec(v_x_1122_);
                        v___x_1157_ = crate::leanh::lean_box(0);
                        v_isShared_1158_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_package_1180_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    v_target_1181_ = crate::leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1205_ = (!crate::leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1205_ == 0 {
                        v___x_1183_ = v_x_1122_;
                        v_isShared_1184_ = v_isSharedCheck_1205_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_target_1181_);
                        crate::leanh::lean_inc(v_package_1180_);
                        crate::leanh::lean_dec(v_x_1122_);
                        v___x_1183_ = crate::leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1205_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v_target_1206_ = crate::leanh::lean_ctor_get(v_x_1122_, 0);
                    v_facet_1207_ = crate::leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1230_ = (!crate::leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1230_ == 0 {
                        v___x_1209_ = v_x_1122_;
                        v_isShared_1210_ = v_isSharedCheck_1230_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_facet_1207_);
                        crate::leanh::lean_inc(v_target_1206_);
                        crate::leanh::lean_dec(v_x_1122_);
                        v___x_1209_ = crate::leanh::lean_box(0);
                        v_isShared_1210_ = v_isSharedCheck_1230_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1127_ = l_Lake_instReprBuildKey_repr___closed__2;
                v___x_1128_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1129_ = l_Lean_Name_reprPrec(v_module_1124_, v___x_1128_);
                v___x_1130_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1130_, 0, v___x_1127_);
                crate::leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
                crate::leanh::lean_inc(v___y_1126_);
                v___x_1131_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1131_, 0, v___y_1126_);
                crate::leanh::lean_ctor_set(v___x_1131_, 1, v___x_1130_);
                v___x_1132_ = 0;
                v___x_1133_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1133_, 0, v___x_1131_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1133_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1132_,
                );
                v___x_1134_ = l_Repr_addAppParen(v___x_1133_, v_prec_1123_);
                return v___x_1134_;
            }
            2 => {
                v___x_1142_ = l_Lake_instReprBuildKey_repr___closed__7;
                v___x_1143_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1144_ = l_Lean_Name_reprPrec(v_package_1139_, v___x_1143_);
                v___x_1145_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_1142_);
                crate::leanh::lean_ctor_set(v___x_1145_, 1, v___x_1144_);
                crate::leanh::lean_inc(v___y_1141_);
                v___x_1146_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1146_, 0, v___y_1141_);
                crate::leanh::lean_ctor_set(v___x_1146_, 1, v___x_1145_);
                v___x_1147_ = 0;
                v___x_1148_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1148_, 0, v___x_1146_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1148_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1147_,
                );
                v___x_1149_ = l_Repr_addAppParen(v___x_1148_, v_prec_1123_);
                return v___x_1149_;
            }
            3 => {
                v___x_1175_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1176_ = lean_nat_dec_le(v___x_1175_, v_prec_1123_);
                if v___x_1176_ == 0 {
                    v___x_1177_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1160_ = v___x_1177_;
                    state = 4;
                    continue;
                } else {
                    v___x_1178_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__4,
                    );
                    v___y_1160_ = v___x_1178_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1161_ = crate::leanh::lean_box(1);
                v___x_1162_ = l_Lake_instReprBuildKey_repr___closed__10;
                v___x_1163_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1164_ = l_Lean_Name_reprPrec(v_package_1154_, v___x_1163_);
                if v_isShared_1158_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1157_, 5);
                    crate::leanh::lean_ctor_set(v___x_1157_, 1, v___x_1164_);
                    crate::leanh::lean_ctor_set(v___x_1157_, 0, v___x_1162_);
                    v___x_1166_ = v___x_1157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1174_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1164_);
                    v___x_1166_ = v_reuseFailAlloc_1174_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1167_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1166_);
                crate::leanh::lean_ctor_set(v___x_1167_, 1, v___x_1161_);
                v___x_1168_ = l_Lean_Name_reprPrec(v_module_1155_, v___x_1163_);
                v___x_1169_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1169_, 0, v___x_1167_);
                crate::leanh::lean_ctor_set(v___x_1169_, 1, v___x_1168_);
                crate::leanh::lean_inc(v___y_1160_);
                v___x_1170_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1170_, 0, v___y_1160_);
                crate::leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
                v___x_1171_ = 0;
                v___x_1172_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1172_, 0, v___x_1170_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1172_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1171_,
                );
                v___x_1173_ = l_Repr_addAppParen(v___x_1172_, v_prec_1123_);
                return v___x_1173_;
            }
            6 => {
                v___x_1201_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1202_ = lean_nat_dec_le(v___x_1201_, v_prec_1123_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1186_ = v___x_1203_;
                    state = 7;
                    continue;
                } else {
                    v___x_1204_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__4,
                    );
                    v___y_1186_ = v___x_1204_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1187_ = crate::leanh::lean_box(1);
                v___x_1188_ = l_Lake_instReprBuildKey_repr___closed__13;
                v___x_1189_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1190_ = l_Lean_Name_reprPrec(v_package_1180_, v___x_1189_);
                if v_isShared_1184_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1183_, 5);
                    crate::leanh::lean_ctor_set(v___x_1183_, 1, v___x_1190_);
                    crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1188_);
                    v___x_1192_ = v___x_1183_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1200_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1190_);
                    v___x_1192_ = v_reuseFailAlloc_1200_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1193_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1193_, 0, v___x_1192_);
                crate::leanh::lean_ctor_set(v___x_1193_, 1, v___x_1187_);
                v___x_1194_ = l_Lean_Name_reprPrec(v_target_1181_, v___x_1189_);
                v___x_1195_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1195_, 0, v___x_1193_);
                crate::leanh::lean_ctor_set(v___x_1195_, 1, v___x_1194_);
                crate::leanh::lean_inc(v___y_1186_);
                v___x_1196_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1196_, 0, v___y_1186_);
                crate::leanh::lean_ctor_set(v___x_1196_, 1, v___x_1195_);
                v___x_1197_ = 0;
                v___x_1198_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1198_, 0, v___x_1196_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1198_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1197_,
                );
                v___x_1199_ = l_Repr_addAppParen(v___x_1198_, v_prec_1123_);
                return v___x_1199_;
            }
            9 => {
                v___x_1211_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_1227_ = lean_nat_dec_le(v___x_1211_, v_prec_1123_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1213_ = v___x_1228_;
                    state = 10;
                    continue;
                } else {
                    v___x_1229_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__4_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__4,
                    );
                    v___y_1213_ = v___x_1229_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1214_ = crate::leanh::lean_box(1);
                v___x_1215_ = l_Lake_instReprBuildKey_repr___closed__16;
                v___x_1216_ = l_Lake_instReprBuildKey_repr(v_target_1206_, v___x_1211_);
                if v_isShared_1210_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1209_, 5);
                    crate::leanh::lean_ctor_set(v___x_1209_, 1, v___x_1216_);
                    crate::leanh::lean_ctor_set(v___x_1209_, 0, v___x_1215_);
                    v___x_1218_ = v___x_1209_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1215_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1216_);
                    v___x_1218_ = v_reuseFailAlloc_1226_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1219_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
                crate::leanh::lean_ctor_set(v___x_1219_, 1, v___x_1214_);
                v___x_1220_ = l_Lean_Name_reprPrec(v_facet_1207_, v___x_1211_);
                v___x_1221_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1221_, 0, v___x_1219_);
                crate::leanh::lean_ctor_set(v___x_1221_, 1, v___x_1220_);
                crate::leanh::lean_inc(v___y_1213_);
                v___x_1222_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1222_, 0, v___y_1213_);
                crate::leanh::lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                v___x_1223_ = 0;
                v___x_1224_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1224_, 0, v___x_1222_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1223_,
                );
                v___x_1225_ = l_Repr_addAppParen(v___x_1224_, v_prec_1123_);
                return v___x_1225_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instReprBuildKey_repr___boxed(
    mut v_x_1231_: *mut crate::leanh::LeanObject,
    mut v_prec_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_Lake_instReprBuildKey_repr(v_x_1231_, v_prec_1232_);
    crate::leanh::lean_dec(v_prec_1232_);
    return v_res_1233_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey_decEq(
    mut v_x_1236_: *mut crate::leanh::LeanObject,
    mut v_x_1237_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_1236_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_x_1237_) == 0 {
                let mut v_module_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: u8 = 0;
                v_module_1238_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                v_module_1239_ = crate::leanh::lean_ctor_get(v_x_1237_, 0);
                v___x_1240_ = lean_name_eq(v_module_1238_, v_module_1239_);
                return v___x_1240_;
            } else {
                let mut v___x_1241_: u8 = 0;
                v___x_1241_ = 0;
                return v___x_1241_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_1237_) == 1 {
                let mut v_package_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1244_: u8 = 0;
                v_package_1242_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                v_package_1243_ = crate::leanh::lean_ctor_get(v_x_1237_, 0);
                v___x_1244_ = lean_name_eq(v_package_1242_, v_package_1243_);
                return v___x_1244_;
            } else {
                let mut v___x_1245_: u8 = 0;
                v___x_1245_ = 0;
                return v___x_1245_;
            }
        }
        2 => {
            if crate::leanh::lean_obj_tag(v_x_1237_) == 2 {
                let mut v_package_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1250_: u8 = 0;
                v_package_1246_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                v_module_1247_ = crate::leanh::lean_ctor_get(v_x_1236_, 1);
                v_package_1248_ = crate::leanh::lean_ctor_get(v_x_1237_, 0);
                v_module_1249_ = crate::leanh::lean_ctor_get(v_x_1237_, 1);
                v___x_1250_ = lean_name_eq(v_package_1246_, v_package_1248_);
                if v___x_1250_ == 0 {
                    return v___x_1250_;
                } else {
                    let mut v___x_1251_: u8 = 0;
                    v___x_1251_ = lean_name_eq(v_module_1247_, v_module_1249_);
                    return v___x_1251_;
                }
            } else {
                let mut v___x_1252_: u8 = 0;
                v___x_1252_ = 0;
                return v___x_1252_;
            }
        }
        3 => {
            if crate::leanh::lean_obj_tag(v_x_1237_) == 3 {
                let mut v_package_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1257_: u8 = 0;
                v_package_1253_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                v_target_1254_ = crate::leanh::lean_ctor_get(v_x_1236_, 1);
                v_package_1255_ = crate::leanh::lean_ctor_get(v_x_1237_, 0);
                v_target_1256_ = crate::leanh::lean_ctor_get(v_x_1237_, 1);
                v___x_1257_ = lean_name_eq(v_package_1253_, v_package_1255_);
                if v___x_1257_ == 0 {
                    return v___x_1257_;
                } else {
                    let mut v___x_1258_: u8 = 0;
                    v___x_1258_ = lean_name_eq(v_target_1254_, v_target_1256_);
                    return v___x_1258_;
                }
            } else {
                let mut v___x_1259_: u8 = 0;
                v___x_1259_ = 0;
                return v___x_1259_;
            }
        }
        _ => {
            if crate::leanh::lean_obj_tag(v_x_1237_) == 4 {
                let mut v_target_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_inst_1264_: u8 = 0;
                v_target_1260_ = crate::leanh::lean_ctor_get(v_x_1236_, 0);
                v_facet_1261_ = crate::leanh::lean_ctor_get(v_x_1236_, 1);
                v_target_1262_ = crate::leanh::lean_ctor_get(v_x_1237_, 0);
                v_facet_1263_ = crate::leanh::lean_ctor_get(v_x_1237_, 1);
                v_inst_1264_ = l_Lake_instDecidableEqBuildKey_decEq(v_target_1260_, v_target_1262_);
                if v_inst_1264_ == 0 {
                    return v_inst_1264_;
                } else {
                    let mut v___x_1265_: u8 = 0;
                    v___x_1265_ = lean_name_eq(v_facet_1261_, v_facet_1263_);
                    return v___x_1265_;
                }
            } else {
                let mut v___x_1266_: u8 = 0;
                v___x_1266_ = 0;
                return v___x_1266_;
            }
        }
    }
}
pub unsafe fn l_Lake_instDecidableEqBuildKey_decEq___boxed(
    mut v_x_1267_: *mut crate::leanh::LeanObject,
    mut v_x_1268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1269_: u8 = 0;
    let mut v_r_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1269_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_1267_, v_x_1268_);
    crate::leanh::lean_dec_ref(v_x_1268_);
    crate::leanh::lean_dec_ref(v_x_1267_);
    v_r_1270_ = crate::leanh::lean_box((v_res_1269_) as usize);
    return v_r_1270_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey(
    mut v_x_1271_: *mut crate::leanh::LeanObject,
    mut v_x_1272_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1273_: u8 = 0;
    v___x_1273_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_1271_, v_x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey___boxed(
    mut v_x_1274_: *mut crate::leanh::LeanObject,
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1276_: u8 = 0;
    let mut v_r_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lake_instDecidableEqBuildKey(v_x_1274_, v_x_1275_);
    crate::leanh::lean_dec_ref(v_x_1275_);
    crate::leanh::lean_dec_ref(v_x_1274_);
    v_r_1277_ = crate::leanh::lean_box((v_res_1276_) as usize);
    return v_r_1277_;
}
pub unsafe fn _init_l_Lake_instHashableBuildKey_hash___closed__0() -> u64 {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u64 = 0;
    v___x_1278_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1279_ = lean_uint64_of_nat(v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Lake_instHashableBuildKey_hash___closed__1() -> u64 {
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    v___x_1280_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
        _init_l_Lake_instHashableBuildKey_hash___closed__0,
    );
    v___x_1281_ = 0u64;
    v___x_1282_ = lean_uint64_mix_hash(v___x_1281_, v___x_1280_);
    return v___x_1282_;
}
pub unsafe fn _init_l_Lake_instHashableBuildKey_hash___closed__2() -> u64 {
    let mut v___x_1283_: u64 = 0;
    let mut v___x_1284_: u64 = 0;
    let mut v___x_1285_: u64 = 0;
    v___x_1283_ = crate::leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
        _init_l_Lake_instHashableBuildKey_hash___closed__0,
    );
    v___x_1284_ = 1u64;
    v___x_1285_ = lean_uint64_mix_hash(v___x_1284_, v___x_1283_);
    return v___x_1285_;
}
pub unsafe fn l_Lake_instHashableBuildKey_hash(
    mut v_x_1286_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_module_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u64 = 0;
    let mut v___x_1289_: u64 = 0;
    let mut v_hash_1290_: u64 = 0;
    let mut v___x_1291_: u64 = 0;
    let mut v_package_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u64 = 0;
    let mut v___x_1294_: u64 = 0;
    let mut v_hash_1295_: u64 = 0;
    let mut v___x_1296_: u64 = 0;
    let mut v_package_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u64 = 0;
    let mut v___y_1301_: u64 = 0;
    let mut v___x_1302_: u64 = 0;
    let mut v___x_1303_: u64 = 0;
    let mut v___x_1304_: u64 = 0;
    let mut v_hash_1305_: u64 = 0;
    let mut v___x_1306_: u64 = 0;
    let mut v___x_1307_: u64 = 0;
    let mut v_hash_1308_: u64 = 0;
    let mut v_package_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u64 = 0;
    let mut v___y_1313_: u64 = 0;
    let mut v___x_1314_: u64 = 0;
    let mut v___x_1315_: u64 = 0;
    let mut v___x_1316_: u64 = 0;
    let mut v_hash_1317_: u64 = 0;
    let mut v___x_1318_: u64 = 0;
    let mut v___x_1319_: u64 = 0;
    let mut v_hash_1320_: u64 = 0;
    let mut v_target_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: u64 = 0;
    let mut v___x_1324_: u64 = 0;
    let mut v___x_1325_: u64 = 0;
    let mut v___x_1326_: u64 = 0;
    let mut v___x_1327_: u64 = 0;
    let mut v_hash_1328_: u64 = 0;
    let mut v___x_1329_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1286_) {
                0 => {
                    v_module_1287_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
                    v___x_1288_ = 0u64;
                    if crate::leanh::lean_obj_tag(v_module_1287_) == 0 {
                        v___x_1289_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__1_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__1,
                        );
                        return v___x_1289_;
                    } else {
                        v_hash_1290_ = crate::leanh::lean_ctor_get_uint64(
                            v_module_1287_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1291_ = lean_uint64_mix_hash(v___x_1288_, v_hash_1290_);
                        return v___x_1291_;
                    }
                }
                1 => {
                    v_package_1292_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
                    v___x_1293_ = 1u64;
                    if crate::leanh::lean_obj_tag(v_package_1292_) == 0 {
                        v___x_1294_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__2_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__2,
                        );
                        return v___x_1294_;
                    } else {
                        v_hash_1295_ = crate::leanh::lean_ctor_get_uint64(
                            v_package_1292_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1296_ = lean_uint64_mix_hash(v___x_1293_, v_hash_1295_);
                        return v___x_1296_;
                    }
                }
                2 => {
                    v_package_1297_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
                    v_module_1298_ = crate::leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1299_ = 2u64;
                    if crate::leanh::lean_obj_tag(v_package_1297_) == 0 {
                        v___x_1307_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__0_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__0,
                        );
                        v___y_1301_ = v___x_1307_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_1308_ = crate::leanh::lean_ctor_get_uint64(
                            v_package_1297_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1301_ = v_hash_1308_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_package_1309_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
                    v_target_1310_ = crate::leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1311_ = 3u64;
                    if crate::leanh::lean_obj_tag(v_package_1309_) == 0 {
                        v___x_1319_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__0_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__0,
                        );
                        v___y_1313_ = v___x_1319_;
                        state = 2;
                        continue;
                    } else {
                        v_hash_1320_ = crate::leanh::lean_ctor_get_uint64(
                            v_package_1309_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1313_ = v_hash_1320_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_target_1321_ = crate::leanh::lean_ctor_get(v_x_1286_, 0);
                    v_facet_1322_ = crate::leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1323_ = 4u64;
                    v___x_1324_ = l_Lake_instHashableBuildKey_hash(v_target_1321_);
                    v___x_1325_ = lean_uint64_mix_hash(v___x_1323_, v___x_1324_);
                    if crate::leanh::lean_obj_tag(v_facet_1322_) == 0 {
                        v___x_1326_ = crate::leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__0_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__0,
                        );
                        v___x_1327_ = lean_uint64_mix_hash(v___x_1325_, v___x_1326_);
                        return v___x_1327_;
                    } else {
                        v_hash_1328_ = crate::leanh::lean_ctor_get_uint64(
                            v_facet_1322_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1329_ = lean_uint64_mix_hash(v___x_1325_, v_hash_1328_);
                        return v___x_1329_;
                    }
                }
            },
            1 => {
                v___x_1302_ = lean_uint64_mix_hash(v___x_1299_, v___y_1301_);
                if crate::leanh::lean_obj_tag(v_module_1298_) == 0 {
                    v___x_1303_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
                        _init_l_Lake_instHashableBuildKey_hash___closed__0,
                    );
                    v___x_1304_ = lean_uint64_mix_hash(v___x_1302_, v___x_1303_);
                    return v___x_1304_;
                } else {
                    v_hash_1305_ = crate::leanh::lean_ctor_get_uint64(
                        v_module_1298_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_1306_ = lean_uint64_mix_hash(v___x_1302_, v_hash_1305_);
                    return v___x_1306_;
                }
            }
            2 => {
                v___x_1314_ = lean_uint64_mix_hash(v___x_1311_, v___y_1313_);
                if crate::leanh::lean_obj_tag(v_target_1310_) == 0 {
                    v___x_1315_ = crate::leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
                        _init_l_Lake_instHashableBuildKey_hash___closed__0,
                    );
                    v___x_1316_ = lean_uint64_mix_hash(v___x_1314_, v___x_1315_);
                    return v___x_1316_;
                } else {
                    v_hash_1317_ = crate::leanh::lean_ctor_get_uint64(
                        v_target_1310_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_1318_ = lean_uint64_mix_hash(v___x_1314_, v_hash_1317_);
                    return v___x_1318_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_instHashableBuildKey_hash___boxed(
    mut v_x_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1331_: u64 = 0;
    let mut v_r_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lake_instHashableBuildKey_hash(v_x_1330_);
    crate::leanh::lean_dec_ref(v_x_1330_);
    v_r_1332_ = crate::leanh::lean_box_uint64(v_res_1331_);
    return v_r_1332_;
}
pub unsafe fn l_Lake_PartialBuildKey_mk(
    mut v_key_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_key_1335_);
    return v_key_1335_;
}
pub unsafe fn l_Lake_PartialBuildKey_mk___boxed(
    mut v_key_1336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Lake_PartialBuildKey_mk(v_key_1336_);
    crate::leanh::lean_dec_ref(v_key_1336_);
    return v_res_1337_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(
    mut v_x_1340_: *mut crate::leanh::LeanObject,
    mut v_prec_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lake_instReprBuildKey_repr(v_x_1340_, v_prec_1341_);
    return v___x_1342_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(
    mut v_x_1343_: *mut crate::leanh::LeanObject,
    mut v_prec_1344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(
        v_x_1343_,
        v_prec_1344_,
    );
    crate::leanh::lean_dec(v_prec_1344_);
    return v_res_1345_;
}
pub unsafe fn _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ =
        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
    v___x_1354_ = lean_string_utf8_byte_size(v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
    mut v_pkg_1358_: *mut crate::leanh::LeanObject,
    mut v_target_1359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1364_: u8 = 0;
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1360_ = crate::leanh::lean_ctor_get(v_target_1359_, 0);
                v_startInclusive_1361_ = crate::leanh::lean_ctor_get(v_target_1359_, 1);
                v_endExclusive_1362_ = crate::leanh::lean_ctor_get(v_target_1359_, 2);
                v___x_1377_ = lean_nat_sub(v_endExclusive_1362_, v_startInclusive_1361_);
                v___x_1378_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1379_ = lean_nat_dec_eq(v___x_1377_, v___x_1378_);
                if v___x_1379_ == 0 {
                    v___x_1380_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1381_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
                    v___x_1382_ = lean_nat_dec_le(v___x_1381_, v___x_1377_);
                    crate::leanh::lean_dec(v___x_1377_);
                    if v___x_1382_ == 0 {
                        v___y_1364_ = v___x_1379_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1383_ = lean_string_memcmp(
                            v_str_1360_,
                            v___x_1380_,
                            v_startInclusive_1361_,
                            v___x_1378_,
                            v___x_1381_,
                        );
                        v___y_1364_ = v___x_1383_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1377_);
                    crate::leanh::lean_dec(v_pkg_1358_);
                    v___x_1384_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3;
                    return v___x_1384_;
                }
            }
            1 => {
                if v___y_1364_ == 0 {
                    v___x_1365_ = lean_string_utf8_extract(
                        v_str_1360_,
                        v_startInclusive_1361_,
                        v_endExclusive_1362_,
                    );
                    v_target_1366_ = l_Lake_stringToLegalOrSimpleName(v___x_1365_);
                    v___x_1367_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1367_, 0, v_pkg_1358_);
                    crate::leanh::lean_ctor_set(v___x_1367_, 1, v_target_1366_);
                    v___x_1368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1368_, 0, v___x_1367_);
                    return v___x_1368_;
                } else {
                    v___x_1369_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1370_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1371_ =
                        l_String_Slice_Pos_nextn(v_target_1359_, v___x_1370_, v___x_1369_);
                    v___x_1372_ = lean_nat_add(v_startInclusive_1361_, v___x_1371_);
                    crate::leanh::lean_dec(v___x_1371_);
                    v___x_1373_ =
                        lean_string_utf8_extract(v_str_1360_, v___x_1372_, v_endExclusive_1362_);
                    crate::leanh::lean_dec(v___x_1372_);
                    v_target_1374_ = l_Lake_stringToLegalOrSimpleName(v___x_1373_);
                    v___x_1375_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1375_, 0, v_pkg_1358_);
                    crate::leanh::lean_ctor_set(v___x_1375_, 1, v_target_1374_);
                    v___x_1376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1376_, 0, v___x_1375_);
                    return v___x_1376_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(
    mut v_pkg_1385_: *mut crate::leanh::LeanObject,
    mut v_target_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
        v_pkg_1385_,
        v_target_1386_,
    );
    crate::leanh::lean_dec_ref(v_target_1386_);
    return v_res_1387_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(
    mut v_s_1390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0;
    return v___x_1391_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(
    mut v_s_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_1392_);
    crate::leanh::lean_dec_ref(v_s_1392_);
    return v_res_1393_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(
    mut v_s_1394_: *mut crate::leanh::LeanObject,
    mut v___x_1395_: *mut crate::leanh::LeanObject,
    mut v___x_1396_: *mut crate::leanh::LeanObject,
    mut v_a_1397_: *mut crate::leanh::LeanObject,
    mut v_b_1398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v_startInclusive_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: u32 = 0;
    let mut v___x_1416_: u32 = 0;
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1397_) == 0 {
                    v_currPos_1406_ = crate::leanh::lean_ctor_get(v_a_1397_, 0);
                    v_searcher_1407_ = crate::leanh::lean_ctor_get(v_a_1397_, 1);
                    v_isSharedCheck_1433_ = (!crate::leanh::lean_is_exclusive(v_a_1397_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1409_ = v_a_1397_;
                        v_isShared_1410_ = v_isSharedCheck_1433_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1407_);
                        crate::leanh::lean_inc(v_currPos_1406_);
                        crate::leanh::lean_dec(v_a_1397_);
                        v___x_1409_ = crate::leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1433_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1396_);
                    crate::leanh::lean_dec_ref(v_s_1394_);
                    return v_b_1398_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_1394_);
                v___x_1403_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1403_, 0, v_s_1394_);
                crate::leanh::lean_ctor_set(v___x_1403_, 1, v_startInclusive_1401_);
                crate::leanh::lean_ctor_set(v___x_1403_, 2, v_endExclusive_1402_);
                v___x_1404_ = lean_array_push(v_b_1398_, v___x_1403_);
                v_a_1397_ = v_it_1400_;
                v_b_1398_ = v___x_1404_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1411_ = crate::leanh::lean_ctor_get(v___x_1395_, 1);
                v_endExclusive_1412_ = crate::leanh::lean_ctor_get(v___x_1395_, 2);
                v___x_1413_ = lean_nat_sub(v_endExclusive_1412_, v_startInclusive_1411_);
                v___x_1414_ = lean_nat_dec_eq(v_searcher_1407_, v___x_1413_);
                crate::leanh::lean_dec(v___x_1413_);
                if v___x_1414_ == 0 {
                    v___x_1415_ = 47;
                    v___x_1416_ = lean_string_utf8_get_fast(v_s_1394_, v_searcher_1407_);
                    v___x_1417_ = lean_uint32_dec_eq(v___x_1416_, v___x_1415_);
                    if v___x_1417_ == 0 {
                        v___x_1418_ = lean_string_utf8_next_fast(v_s_1394_, v_searcher_1407_);
                        crate::leanh::lean_dec(v_searcher_1407_);
                        if v_isShared_1410_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1418_);
                            v___x_1420_ = v___x_1409_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1422_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_currPos_1406_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1418_);
                            v___x_1420_ = v_reuseFailAlloc_1422_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1423_ = lean_string_utf8_next_fast(v_s_1394_, v_searcher_1407_);
                        v___x_1424_ = lean_nat_sub(v___x_1423_, v_searcher_1407_);
                        v___x_1425_ = lean_nat_add(v_searcher_1407_, v___x_1424_);
                        crate::leanh::lean_dec(v___x_1424_);
                        v_slice_1426_ = l_String_Slice_subslice_x21(
                            v___x_1395_,
                            v_currPos_1406_,
                            v_searcher_1407_,
                        );
                        crate::leanh::lean_inc(v___x_1425_);
                        if v_isShared_1410_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1409_, 1, v___x_1425_);
                            crate::leanh::lean_ctor_set(v___x_1409_, 0, v___x_1425_);
                            v_nextIt_1428_ = v___x_1409_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1431_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1425_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1425_);
                            v_nextIt_1428_ = v_reuseFailAlloc_1431_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1409_);
                    crate::leanh::lean_dec(v_searcher_1407_);
                    v___x_1432_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1396_);
                    v_it_1400_ = v___x_1432_;
                    v_startInclusive_1401_ = v_currPos_1406_;
                    v_endExclusive_1402_ = v___x_1396_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1397_ = v___x_1420_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1429_ = crate::leanh::lean_ctor_get(v_slice_1426_, 0);
                crate::leanh::lean_inc(v_startInclusive_1429_);
                v_endExclusive_1430_ = crate::leanh::lean_ctor_get(v_slice_1426_, 1);
                crate::leanh::lean_inc(v_endExclusive_1430_);
                crate::leanh::lean_dec_ref(v_slice_1426_);
                v_it_1400_ = v_nextIt_1428_;
                v_startInclusive_1401_ = v_startInclusive_1429_;
                v_endExclusive_1402_ = v_endExclusive_1430_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg___boxed(
    mut v_s_1434_: *mut crate::leanh::LeanObject,
    mut v___x_1435_: *mut crate::leanh::LeanObject,
    mut v___x_1436_: *mut crate::leanh::LeanObject,
    mut v_a_1437_: *mut crate::leanh::LeanObject,
    mut v_b_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1434_, v___x_1435_, v___x_1436_, v_a_1437_, v_b_1438_);
    crate::leanh::lean_dec_ref(v___x_1435_);
    return v_res_1439_;
}
pub unsafe fn _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
    v___x_1452_ = lean_string_utf8_byte_size(v___x_1451_);
    return v___x_1452_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(
    mut v_s_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: u8 = 0;
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1457_ = lean_string_utf8_byte_size(v_s_1453_);
                crate::leanh::lean_inc_ref(v_s_1453_);
                v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1458_, 0, v_s_1453_);
                crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
                crate::leanh::lean_ctor_set(v___x_1458_, 2, v___x_1457_);
                v___x_1459_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v___x_1458_);
                v___x_1460_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2;
                v___x_1461_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1453_, v___x_1458_, v___x_1457_, v___x_1459_, v___x_1460_);
                crate::leanh::lean_dec_ref_known(v___x_1458_, 3);
                v___x_1462_ = lean_array_to_list(v___x_1461_);
                if crate::leanh::lean_obj_tag(v___x_1462_) == 1 {
                    v_head_1463_ = crate::leanh::lean_ctor_get(v___x_1462_, 0);
                    crate::leanh::lean_inc(v_head_1463_);
                    v_tail_1464_ = crate::leanh::lean_ctor_get(v___x_1462_, 1);
                    crate::leanh::lean_inc(v_tail_1464_);
                    crate::leanh::lean_dec_ref_known(v___x_1462_, 2);
                    if crate::leanh::lean_obj_tag(v_tail_1464_) == 0 {
                        v_str_1468_ = crate::leanh::lean_ctor_get(v_head_1463_, 0);
                        v_startInclusive_1469_ = crate::leanh::lean_ctor_get(v_head_1463_, 1);
                        v_endExclusive_1470_ = crate::leanh::lean_ctor_get(v_head_1463_, 2);
                        v___x_1498_ = lean_nat_sub(v_endExclusive_1470_, v_startInclusive_1469_);
                        v___x_1499_ = lean_nat_dec_eq(v___x_1498_, v___x_1456_);
                        if v___x_1499_ == 0 {
                            v___x_1500_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
                            v___x_1501_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
                            v___x_1502_ = lean_nat_dec_le(v___x_1501_, v___x_1498_);
                            crate::leanh::lean_dec(v___x_1498_);
                            if v___x_1502_ == 0 {
                                v___y_1472_ = v___x_1499_;
                                state = 3;
                                continue;
                            } else {
                                v___x_1503_ = lean_string_memcmp(
                                    v_str_1468_,
                                    v___x_1500_,
                                    v_startInclusive_1469_,
                                    v___x_1456_,
                                    v___x_1501_,
                                );
                                v___y_1472_ = v___x_1503_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_1498_);
                            crate::leanh::lean_dec(v_head_1463_);
                            v___x_1504_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5;
                            return v___x_1504_;
                        }
                    } else {
                        v_head_1505_ = crate::leanh::lean_ctor_get(v_tail_1464_, 0);
                        crate::leanh::lean_inc(v_head_1505_);
                        v_tail_1506_ = crate::leanh::lean_ctor_get(v_tail_1464_, 1);
                        crate::leanh::lean_inc(v_tail_1506_);
                        crate::leanh::lean_dec_ref_known(v_tail_1464_, 2);
                        if crate::leanh::lean_obj_tag(v_tail_1506_) == 0 {
                            v_str_1518_ = crate::leanh::lean_ctor_get(v_head_1463_, 0);
                            crate::leanh::lean_inc_ref(v_str_1518_);
                            v_startInclusive_1519_ = crate::leanh::lean_ctor_get(v_head_1463_, 1);
                            crate::leanh::lean_inc(v_startInclusive_1519_);
                            v_endExclusive_1520_ = crate::leanh::lean_ctor_get(v_head_1463_, 2);
                            crate::leanh::lean_inc(v_endExclusive_1520_);
                            v___x_1521_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
                            v___x_1522_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
                            v___x_1523_ =
                                lean_nat_sub(v_endExclusive_1520_, v_startInclusive_1519_);
                            v___x_1524_ = lean_nat_dec_le(v___x_1522_, v___x_1523_);
                            crate::leanh::lean_dec(v___x_1523_);
                            if v___x_1524_ == 0 {
                                crate::leanh::lean_dec(v_head_1463_);
                                v_str_1508_ = v_str_1518_;
                                v_startInclusive_1509_ = v_startInclusive_1519_;
                                v_endExclusive_1510_ = v_endExclusive_1520_;
                                state = 4;
                                continue;
                            } else {
                                v___x_1525_ = lean_string_memcmp(
                                    v_str_1518_,
                                    v___x_1521_,
                                    v_startInclusive_1519_,
                                    v___x_1456_,
                                    v___x_1522_,
                                );
                                if v___x_1525_ == 0 {
                                    crate::leanh::lean_dec(v_head_1463_);
                                    v_str_1508_ = v_str_1518_;
                                    v_startInclusive_1509_ = v_startInclusive_1519_;
                                    v_endExclusive_1510_ = v_endExclusive_1520_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_1526_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1527_ = l_String_Slice_Pos_nextn(
                                        v_head_1463_,
                                        v___x_1456_,
                                        v___x_1526_,
                                    );
                                    crate::leanh::lean_dec(v_head_1463_);
                                    v___x_1528_ = lean_nat_add(v_startInclusive_1519_, v___x_1527_);
                                    crate::leanh::lean_dec(v___x_1527_);
                                    crate::leanh::lean_dec(v_startInclusive_1519_);
                                    v_str_1508_ = v_str_1518_;
                                    v_startInclusive_1509_ = v___x_1528_;
                                    v_endExclusive_1510_ = v_endExclusive_1520_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_tail_1506_);
                            crate::leanh::lean_dec(v_head_1505_);
                            crate::leanh::lean_dec(v_head_1463_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1462_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1455_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1;
                return v___x_1455_;
            }
            2 => {
                v___x_1466_ = crate::leanh::lean_box(0);
                v___x_1467_ =
                    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                        v___x_1466_,
                        v_head_1463_,
                    );
                crate::leanh::lean_dec(v_head_1463_);
                return v___x_1467_;
            }
            3 => {
                if v___y_1472_ == 0 {
                    v___x_1473_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1474_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
                    v___x_1475_ = lean_nat_sub(v_endExclusive_1470_, v_startInclusive_1469_);
                    v___x_1476_ = lean_nat_dec_le(v___x_1474_, v___x_1475_);
                    crate::leanh::lean_dec(v___x_1475_);
                    if v___x_1476_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1477_ = lean_string_memcmp(
                            v_str_1468_,
                            v___x_1473_,
                            v_startInclusive_1469_,
                            v___x_1456_,
                            v___x_1474_,
                        );
                        if v___x_1477_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_endExclusive_1470_);
                            crate::leanh::lean_inc(v_startInclusive_1469_);
                            crate::leanh::lean_inc_ref(v_str_1468_);
                            v___x_1478_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1479_ =
                                l_String_Slice_Pos_nextn(v_head_1463_, v___x_1456_, v___x_1478_);
                            crate::leanh::lean_dec(v_head_1463_);
                            v___x_1480_ = lean_nat_add(v_startInclusive_1469_, v___x_1479_);
                            crate::leanh::lean_dec(v___x_1479_);
                            crate::leanh::lean_dec(v_startInclusive_1469_);
                            v___x_1481_ = lean_nat_sub(v_endExclusive_1470_, v___x_1480_);
                            v___x_1482_ = lean_nat_dec_eq(v___x_1481_, v___x_1456_);
                            crate::leanh::lean_dec(v___x_1481_);
                            if v___x_1482_ == 0 {
                                v___x_1483_ = lean_string_utf8_extract(
                                    v_str_1468_,
                                    v___x_1480_,
                                    v_endExclusive_1470_,
                                );
                                crate::leanh::lean_dec(v_endExclusive_1470_);
                                crate::leanh::lean_dec(v___x_1480_);
                                crate::leanh::lean_dec_ref(v_str_1468_);
                                v___x_1484_ = l_Lake_stringToLegalOrSimpleName(v___x_1483_);
                                v___x_1485_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                                v___x_1486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                                return v___x_1486_;
                            } else {
                                crate::leanh::lean_dec(v___x_1480_);
                                crate::leanh::lean_dec(v_endExclusive_1470_);
                                crate::leanh::lean_dec_ref(v_str_1468_);
                                v___x_1487_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4;
                                return v___x_1487_;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_endExclusive_1470_);
                    crate::leanh::lean_inc(v_startInclusive_1469_);
                    crate::leanh::lean_inc_ref(v_str_1468_);
                    v___x_1488_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1489_ = l_String_Slice_Pos_nextn(v_head_1463_, v___x_1456_, v___x_1488_);
                    crate::leanh::lean_dec(v_head_1463_);
                    v___x_1490_ = lean_nat_add(v_startInclusive_1469_, v___x_1489_);
                    crate::leanh::lean_dec(v___x_1489_);
                    crate::leanh::lean_dec(v_startInclusive_1469_);
                    v___x_1491_ = lean_nat_sub(v_endExclusive_1470_, v___x_1490_);
                    v___x_1492_ = lean_nat_dec_eq(v___x_1491_, v___x_1456_);
                    crate::leanh::lean_dec(v___x_1491_);
                    if v___x_1492_ == 0 {
                        v___x_1493_ = lean_string_utf8_extract(
                            v_str_1468_,
                            v___x_1490_,
                            v_endExclusive_1470_,
                        );
                        crate::leanh::lean_dec(v_endExclusive_1470_);
                        crate::leanh::lean_dec(v___x_1490_);
                        crate::leanh::lean_dec_ref(v_str_1468_);
                        v___x_1494_ = l_Lake_stringToLegalOrSimpleName(v___x_1493_);
                        v___x_1495_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                        v___x_1496_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1496_, 0, v___x_1495_);
                        return v___x_1496_;
                    } else {
                        crate::leanh::lean_dec(v___x_1490_);
                        crate::leanh::lean_dec(v_endExclusive_1470_);
                        crate::leanh::lean_dec_ref(v_str_1468_);
                        v___x_1497_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5;
                        return v___x_1497_;
                    }
                }
            }
            4 => {
                v___x_1511_ = lean_nat_sub(v_endExclusive_1510_, v_startInclusive_1509_);
                v___x_1512_ = lean_nat_dec_eq(v___x_1511_, v___x_1456_);
                crate::leanh::lean_dec(v___x_1511_);
                if v___x_1512_ == 0 {
                    v___x_1513_ = lean_string_utf8_extract(
                        v_str_1508_,
                        v_startInclusive_1509_,
                        v_endExclusive_1510_,
                    );
                    crate::leanh::lean_dec(v_endExclusive_1510_);
                    crate::leanh::lean_dec(v_startInclusive_1509_);
                    crate::leanh::lean_dec_ref(v_str_1508_);
                    v___x_1514_ = l_Lake_stringToLegalOrSimpleName(v___x_1513_);
                    v___x_1515_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                            v___x_1514_,
                            v_head_1505_,
                        );
                    crate::leanh::lean_dec(v_head_1505_);
                    return v___x_1515_;
                } else {
                    crate::leanh::lean_dec(v_endExclusive_1510_);
                    crate::leanh::lean_dec(v_startInclusive_1509_);
                    crate::leanh::lean_dec_ref(v_str_1508_);
                    v___x_1516_ = crate::leanh::lean_box(0);
                    v___x_1517_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                            v___x_1516_,
                            v_head_1505_,
                        );
                    crate::leanh::lean_dec(v_head_1505_);
                    return v___x_1517_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(
    mut v_s_1529_: *mut crate::leanh::LeanObject,
    mut v___x_1530_: *mut crate::leanh::LeanObject,
    mut v___x_1531_: *mut crate::leanh::LeanObject,
    mut v_inst_1532_: *mut crate::leanh::LeanObject,
    mut v_R_1533_: *mut crate::leanh::LeanObject,
    mut v_a_1534_: *mut crate::leanh::LeanObject,
    mut v_b_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1529_, v___x_1530_, v___x_1531_, v_a_1534_, v_b_1535_);
    return v___x_1536_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(
    mut v_s_1537_: *mut crate::leanh::LeanObject,
    mut v___x_1538_: *mut crate::leanh::LeanObject,
    mut v___x_1539_: *mut crate::leanh::LeanObject,
    mut v_inst_1540_: *mut crate::leanh::LeanObject,
    mut v_R_1541_: *mut crate::leanh::LeanObject,
    mut v_a_1542_: *mut crate::leanh::LeanObject,
    mut v_b_1543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1544_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_1537_, v___x_1538_, v___x_1539_, v_inst_1540_, v_R_1541_, v_a_1542_, v_b_1543_);
    crate::leanh::lean_dec_ref(v___x_1538_);
    return v_res_1544_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(
    mut v_s_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0;
    return v___x_1546_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(
    mut v_s_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ =
        l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_1547_);
    crate::leanh::lean_dec_ref(v_s_1547_);
    return v_res_1548_;
}
pub unsafe fn l_panic___at___00Lake_PartialBuildKey_parse_spec__2(
    mut v_msg_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0;
    v___x_1552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1552_, 0, v___x_1551_);
    v___x_1553_ = lean_panic_fn_borrowed(v___x_1552_, v_msg_1550_);
    crate::leanh::lean_dec_ref_known(v___x_1552_, 1);
    return v___x_1553_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(
    mut v_s_1554_: *mut crate::leanh::LeanObject,
    mut v___x_1555_: *mut crate::leanh::LeanObject,
    mut v___x_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_b_1558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_it_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v_startInclusive_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: u32 = 0;
    let mut v___x_1577_: u32 = 0;
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1557_) == 0 {
                    v_currPos_1567_ = crate::leanh::lean_ctor_get(v_a_1557_, 0);
                    v_searcher_1568_ = crate::leanh::lean_ctor_get(v_a_1557_, 1);
                    v_isSharedCheck_1594_ = (!crate::leanh::lean_is_exclusive(v_a_1557_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1570_ = v_a_1557_;
                        v_isShared_1571_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_searcher_1568_);
                        crate::leanh::lean_inc(v_currPos_1567_);
                        crate::leanh::lean_dec(v_a_1557_);
                        v___x_1570_ = crate::leanh::lean_box(0);
                        v_isShared_1571_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1556_);
                    crate::leanh::lean_dec_ref(v_s_1554_);
                    return v_b_1558_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_s_1554_);
                v___x_1563_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1563_, 0, v_s_1554_);
                crate::leanh::lean_ctor_set(v___x_1563_, 1, v_startInclusive_1561_);
                crate::leanh::lean_ctor_set(v___x_1563_, 2, v_endExclusive_1562_);
                v___x_1564_ = l_String_Slice_toString(v___x_1563_);
                crate::leanh::lean_dec_ref_known(v___x_1563_, 3);
                v___x_1565_ = lean_array_push(v_b_1558_, v___x_1564_);
                v_a_1557_ = v_it_1560_;
                v_b_1558_ = v___x_1565_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1572_ = crate::leanh::lean_ctor_get(v___x_1555_, 1);
                v_endExclusive_1573_ = crate::leanh::lean_ctor_get(v___x_1555_, 2);
                v___x_1574_ = lean_nat_sub(v_endExclusive_1573_, v_startInclusive_1572_);
                v___x_1575_ = lean_nat_dec_eq(v_searcher_1568_, v___x_1574_);
                crate::leanh::lean_dec(v___x_1574_);
                if v___x_1575_ == 0 {
                    v___x_1576_ = 58;
                    v___x_1577_ = lean_string_utf8_get_fast(v_s_1554_, v_searcher_1568_);
                    v___x_1578_ = lean_uint32_dec_eq(v___x_1577_, v___x_1576_);
                    if v___x_1578_ == 0 {
                        v___x_1579_ = lean_string_utf8_next_fast(v_s_1554_, v_searcher_1568_);
                        crate::leanh::lean_dec(v_searcher_1568_);
                        if v_isShared_1571_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1570_, 1, v___x_1579_);
                            v___x_1581_ = v___x_1570_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1583_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_currPos_1567_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1579_);
                            v___x_1581_ = v_reuseFailAlloc_1583_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1584_ = lean_string_utf8_next_fast(v_s_1554_, v_searcher_1568_);
                        v___x_1585_ = lean_nat_sub(v___x_1584_, v_searcher_1568_);
                        v___x_1586_ = lean_nat_add(v_searcher_1568_, v___x_1585_);
                        crate::leanh::lean_dec(v___x_1585_);
                        v_slice_1587_ = l_String_Slice_subslice_x21(
                            v___x_1555_,
                            v_currPos_1567_,
                            v_searcher_1568_,
                        );
                        crate::leanh::lean_inc(v___x_1586_);
                        if v_isShared_1571_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1570_, 1, v___x_1586_);
                            crate::leanh::lean_ctor_set(v___x_1570_, 0, v___x_1586_);
                            v_nextIt_1589_ = v___x_1570_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1592_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1586_);
                            v_nextIt_1589_ = v_reuseFailAlloc_1592_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1570_);
                    crate::leanh::lean_dec(v_searcher_1568_);
                    v___x_1593_ = crate::leanh::lean_box(1);
                    crate::leanh::lean_inc(v___x_1556_);
                    v_it_1560_ = v___x_1593_;
                    v_startInclusive_1561_ = v_currPos_1567_;
                    v_endExclusive_1562_ = v___x_1556_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1557_ = v___x_1581_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1590_ = crate::leanh::lean_ctor_get(v_slice_1587_, 0);
                crate::leanh::lean_inc(v_startInclusive_1590_);
                v_endExclusive_1591_ = crate::leanh::lean_ctor_get(v_slice_1587_, 1);
                crate::leanh::lean_inc(v_endExclusive_1591_);
                crate::leanh::lean_dec_ref(v_slice_1587_);
                v_it_1560_ = v_nextIt_1589_;
                v_startInclusive_1561_ = v_startInclusive_1590_;
                v_endExclusive_1562_ = v_endExclusive_1591_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg___boxed(
    mut v_s_1595_: *mut crate::leanh::LeanObject,
    mut v___x_1596_: *mut crate::leanh::LeanObject,
    mut v___x_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
    mut v_b_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1595_, v___x_1596_, v___x_1597_, v_a_1598_, v_b_1599_);
    crate::leanh::lean_dec_ref(v___x_1596_);
    return v_res_1600_;
}
pub unsafe fn l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_x_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1605_) == 0 {
                    v___x_1606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1606_, 0, v_x_1604_);
                    return v___x_1606_;
                } else {
                    v_head_1607_ = crate::leanh::lean_ctor_get(v_x_1605_, 0);
                    v_tail_1608_ = crate::leanh::lean_ctor_get(v_x_1605_, 1);
                    v_isSharedCheck_1621_ = (!crate::leanh::lean_is_exclusive(v_x_1605_)) as u8;
                    if v_isSharedCheck_1621_ == 0 {
                        v___x_1610_ = v_x_1605_;
                        v_isShared_1611_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1608_);
                        crate::leanh::lean_inc(v_head_1607_);
                        crate::leanh::lean_dec(v_x_1605_);
                        v___x_1610_ = crate::leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = lean_string_utf8_byte_size(v_head_1607_);
                v___x_1613_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1614_ = lean_nat_dec_eq(v___x_1612_, v___x_1613_);
                if v___x_1614_ == 0 {
                    v___x_1615_ = l_Lake_stringToLegalOrSimpleName(v_head_1607_);
                    if v_isShared_1611_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1610_, 4);
                        crate::leanh::lean_ctor_set(v___x_1610_, 1, v___x_1615_);
                        crate::leanh::lean_ctor_set(v___x_1610_, 0, v_x_1604_);
                        v___x_1617_ = v___x_1610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1619_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_x_1604_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1615_);
                        v___x_1617_ = v_reuseFailAlloc_1619_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1610_);
                    crate::leanh::lean_dec(v_tail_1608_);
                    crate::leanh::lean_dec(v_head_1607_);
                    crate::leanh::lean_dec_ref(v_x_1604_);
                    v___x_1620_ =
                        l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1;
                    return v___x_1620_;
                }
            }
            2 => {
                v_x_1604_ = v___x_1617_;
                v_x_1605_ = v_tail_1608_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_PartialBuildKey_parse___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lake_PartialBuildKey_parse___closed__3;
    v___x_1628_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_1629_ = crate::leanh::lean_unsigned_to_nat(65);
    v___x_1630_ = l_Lake_PartialBuildKey_parse___closed__2;
    v___x_1631_ = l_Lake_PartialBuildKey_parse___closed__1;
    v___x_1632_ = l_mkPanicMessageWithDecl(
        v___x_1631_,
        v___x_1630_,
        v___x_1629_,
        v___x_1628_,
        v___x_1627_,
    );
    return v___x_1632_;
}
pub unsafe fn l_Lake_PartialBuildKey_parse(
    mut v_s_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    v___x_1637_ = lean_string_utf8_byte_size(v_s_1636_);
    v___x_1638_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
    if v___x_1639_ == 0 {
        let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc_ref(v_s_1636_);
        v___x_1640_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1640_, 0, v_s_1636_);
        crate::leanh::lean_ctor_set(v___x_1640_, 1, v___x_1638_);
        crate::leanh::lean_ctor_set(v___x_1640_, 2, v___x_1637_);
        v___x_1641_ =
            l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_1640_);
        v___x_1642_ = l_Lake_PartialBuildKey_parse___closed__0;
        v___x_1643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1636_, v___x_1640_, v___x_1637_, v___x_1641_, v___x_1642_);
        crate::leanh::lean_dec_ref_known(v___x_1640_, 3);
        v___x_1644_ = lean_array_to_list(v___x_1643_);
        if crate::leanh::lean_obj_tag(v___x_1644_) == 0 {
            let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1645_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_PartialBuildKey_parse___closed__4),
                core::ptr::addr_of_mut!(l_Lake_PartialBuildKey_parse___closed__4_once),
                _init_l_Lake_PartialBuildKey_parse___closed__4,
            );
            v___x_1646_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_1645_);
            return v___x_1646_;
        } else {
            let mut v_head_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_1647_ = crate::leanh::lean_ctor_get(v___x_1644_, 0);
            crate::leanh::lean_inc(v_head_1647_);
            v_tail_1648_ = crate::leanh::lean_ctor_get(v___x_1644_, 1);
            crate::leanh::lean_inc(v_tail_1648_);
            crate::leanh::lean_dec_ref_known(v___x_1644_, 2);
            v___x_1649_ =
                l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_1647_);
            if crate::leanh::lean_obj_tag(v___x_1649_) == 0 {
                crate::leanh::lean_dec(v_tail_1648_);
                return v___x_1649_;
            } else {
                let mut v_a_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1650_ = crate::leanh::lean_ctor_get(v___x_1649_, 0);
                crate::leanh::lean_inc(v_a_1650_);
                crate::leanh::lean_dec_ref_known(v___x_1649_, 1);
                v___x_1651_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(
                    v_a_1650_,
                    v_tail_1648_,
                );
                return v___x_1651_;
            }
        }
    } else {
        let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1636_);
        v___x_1652_ = l_Lake_PartialBuildKey_parse___closed__6;
        return v___x_1652_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(
    mut v_s_1653_: *mut crate::leanh::LeanObject,
    mut v___x_1654_: *mut crate::leanh::LeanObject,
    mut v___x_1655_: *mut crate::leanh::LeanObject,
    mut v_inst_1656_: *mut crate::leanh::LeanObject,
    mut v_R_1657_: *mut crate::leanh::LeanObject,
    mut v_a_1658_: *mut crate::leanh::LeanObject,
    mut v_b_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1653_, v___x_1654_, v___x_1655_, v_a_1658_, v_b_1659_);
    return v___x_1660_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(
    mut v_s_1661_: *mut crate::leanh::LeanObject,
    mut v___x_1662_: *mut crate::leanh::LeanObject,
    mut v___x_1663_: *mut crate::leanh::LeanObject,
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_R_1665_: *mut crate::leanh::LeanObject,
    mut v_a_1666_: *mut crate::leanh::LeanObject,
    mut v_b_1667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_1661_, v___x_1662_, v___x_1663_, v_inst_1664_, v_R_1665_, v_a_1666_, v_b_1667_);
    crate::leanh::lean_dec_ref(v___x_1662_);
    return v_res_1668_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
    mut v_p_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_p_1669_) {
        0 => {
            return v_p_1669_;
        }
        2 => {
            let mut v_pre_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_1670_ = crate::leanh::lean_ctor_get(v_p_1669_, 0);
            if crate::leanh::lean_obj_tag(v_pre_1670_) == 0 {
                return v_pre_1670_;
            } else {
                crate::leanh::lean_inc(v_pre_1670_);
                return v_pre_1670_;
            }
        }
        _ => {
            crate::leanh::lean_inc(v_p_1669_);
            return v_p_1669_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(
    mut v_p_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_1671_);
    crate::leanh::lean_dec(v_p_1671_);
    return v_res_1672_;
}
pub unsafe fn l_Lake_PartialBuildKey_toString(
    mut v_x_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_module_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1676_) {
                0 => {
                    v_module_1677_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
                    crate::leanh::lean_inc(v_module_1677_);
                    crate::leanh::lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1678_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1679_ = 1;
                    v___x_1680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1677_,
                        v___x_1679_,
                    );
                    v___x_1681_ = lean_string_append(v___x_1678_, v___x_1680_);
                    crate::leanh::lean_dec_ref(v___x_1680_);
                    return v___x_1681_;
                }
                1 => {
                    v_package_1682_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
                    crate::leanh::lean_inc(v_package_1682_);
                    crate::leanh::lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1683_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1682_,
                        );
                    crate::leanh::lean_dec(v_package_1682_);
                    if crate::leanh::lean_obj_tag(v___x_1683_) == 0 {
                        v___x_1684_ =
                            l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0;
                        return v___x_1684_;
                    } else {
                        v___x_1685_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
                        v___x_1686_ = 1;
                        v___x_1687_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_1683_,
                                v___x_1686_,
                            );
                        v___x_1688_ = lean_string_append(v___x_1685_, v___x_1687_);
                        crate::leanh::lean_dec_ref(v___x_1687_);
                        return v___x_1688_;
                    }
                }
                2 => {
                    v_package_1689_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
                    crate::leanh::lean_inc(v_package_1689_);
                    v_module_1690_ = crate::leanh::lean_ctor_get(v_x_1676_, 1);
                    crate::leanh::lean_inc(v_module_1690_);
                    crate::leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1691_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1689_,
                        );
                    crate::leanh::lean_dec(v_package_1689_);
                    if crate::leanh::lean_obj_tag(v___x_1691_) == 0 {
                        v___x_1692_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                        v___x_1693_ = 1;
                        v___x_1694_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_module_1690_,
                                v___x_1693_,
                            );
                        v___x_1695_ = lean_string_append(v___x_1692_, v___x_1694_);
                        crate::leanh::lean_dec_ref(v___x_1694_);
                        return v___x_1695_;
                    } else {
                        v___x_1696_ = 1;
                        v___x_1697_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_1691_,
                                v___x_1696_,
                            );
                        v___x_1698_ = l_Lake_PartialBuildKey_toString___closed__0;
                        v___x_1699_ = lean_string_append(v___x_1697_, v___x_1698_);
                        v___x_1700_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_module_1690_,
                                v___x_1696_,
                            );
                        v___x_1701_ = lean_string_append(v___x_1699_, v___x_1700_);
                        crate::leanh::lean_dec_ref(v___x_1700_);
                        return v___x_1701_;
                    }
                }
                3 => {
                    v_package_1702_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
                    crate::leanh::lean_inc(v_package_1702_);
                    v_target_1703_ = crate::leanh::lean_ctor_get(v_x_1676_, 1);
                    crate::leanh::lean_inc(v_target_1703_);
                    crate::leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1704_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1702_,
                        );
                    crate::leanh::lean_dec(v_package_1702_);
                    if crate::leanh::lean_obj_tag(v___x_1704_) == 0 {
                        v___x_1705_ = 1;
                        v___x_1706_ = l_Lean_Name_toString(v_target_1703_, v___x_1705_);
                        return v___x_1706_;
                    } else {
                        v___x_1707_ = 1;
                        v___x_1708_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_1704_,
                                v___x_1707_,
                            );
                        v___x_1709_ = l_Lake_PartialBuildKey_toString___closed__1;
                        v___x_1710_ = lean_string_append(v___x_1708_, v___x_1709_);
                        v___x_1711_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_target_1703_,
                                v___x_1707_,
                            );
                        v___x_1712_ = lean_string_append(v___x_1710_, v___x_1711_);
                        crate::leanh::lean_dec_ref(v___x_1711_);
                        return v___x_1712_;
                    }
                }
                _ => {
                    v_target_1713_ = crate::leanh::lean_ctor_get(v_x_1676_, 0);
                    crate::leanh::lean_inc_ref(v_target_1713_);
                    v_facet_1714_ = crate::leanh::lean_ctor_get(v_x_1676_, 1);
                    crate::leanh::lean_inc(v_facet_1714_);
                    crate::leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1715_ = l_Lean_Name_isAnonymous(v_facet_1714_);
                    if v___x_1715_ == 0 {
                        v___x_1716_ = l_Lake_PartialBuildKey_toString(v_target_1713_);
                        v___x_1717_ = l_Lake_PartialBuildKey_toString___closed__2;
                        v___x_1718_ = lean_string_append(v___x_1716_, v___x_1717_);
                        v___x_1719_ = 1;
                        v___x_1720_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_facet_1714_,
                                v___x_1719_,
                            );
                        v___x_1721_ = lean_string_append(v___x_1718_, v___x_1720_);
                        crate::leanh::lean_dec_ref(v___x_1720_);
                        return v___x_1721_;
                    } else {
                        crate::leanh::lean_dec(v_facet_1714_);
                        v_x_1676_ = v_target_1713_;
                        state = 0;
                        continue;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildKey_moduleFacet(
    mut v_module_1725_: *mut crate::leanh::LeanObject,
    mut v_facet_1726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1727_, 0, v_module_1725_);
    v___x_1728_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    crate::leanh::lean_ctor_set(v___x_1728_, 1, v_facet_1726_);
    return v___x_1728_;
}
pub unsafe fn l_Lake_BuildKey_packageFacet(
    mut v_package_1729_: *mut crate::leanh::LeanObject,
    mut v_facet_1730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1731_, 0, v_package_1729_);
    v___x_1732_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1732_, 0, v___x_1731_);
    crate::leanh::lean_ctor_set(v___x_1732_, 1, v_facet_1730_);
    return v___x_1732_;
}
pub unsafe fn l_Lake_BuildKey_packageModuleFacet(
    mut v_package_1733_: *mut crate::leanh::LeanObject,
    mut v_module_1734_: *mut crate::leanh::LeanObject,
    mut v_facet_1735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1736_, 0, v_package_1733_);
    crate::leanh::lean_ctor_set(v___x_1736_, 1, v_module_1734_);
    v___x_1737_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1737_, 1, v_facet_1735_);
    return v___x_1737_;
}
pub unsafe fn l_Lake_BuildKey_targetFacet(
    mut v_package_1738_: *mut crate::leanh::LeanObject,
    mut v_target_1739_: *mut crate::leanh::LeanObject,
    mut v_facet_1740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1741_, 0, v_package_1738_);
    crate::leanh::lean_ctor_set(v___x_1741_, 1, v_target_1739_);
    v___x_1742_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1741_);
    crate::leanh::lean_ctor_set(v___x_1742_, 1, v_facet_1740_);
    return v___x_1742_;
}
pub unsafe fn l_Lake_BuildKey_customTarget(
    mut v_package_1743_: *mut crate::leanh::LeanObject,
    mut v_target_1744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1745_, 0, v_package_1743_);
    crate::leanh::lean_ctor_set(v___x_1745_, 1, v_target_1744_);
    return v___x_1745_;
}
pub unsafe fn l_Lake_BuildKey_toString(
    mut v_x_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1746_) {
        0 => {
            let mut v_module_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: u8 = 0;
            let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_module_1747_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
            crate::leanh::lean_inc(v_module_1747_);
            crate::leanh::lean_dec_ref_known(v_x_1746_, 1);
            v___x_1748_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
            v___x_1749_ = 1;
            v___x_1750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_module_1747_,
                v___x_1749_,
            );
            v___x_1751_ = lean_string_append(v___x_1748_, v___x_1750_);
            crate::leanh::lean_dec_ref(v___x_1750_);
            return v___x_1751_;
        }
        1 => {
            let mut v_package_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1755_: u8 = 0;
            let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_package_1752_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
            crate::leanh::lean_inc(v_package_1752_);
            crate::leanh::lean_dec_ref_known(v_x_1746_, 1);
            v___x_1753_ =
                l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
            v___x_1754_ = l_Lean_Name_getPrefix(v_package_1752_);
            crate::leanh::lean_dec(v_package_1752_);
            v___x_1755_ = 1;
            v___x_1756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_1754_,
                v___x_1755_,
            );
            v___x_1757_ = lean_string_append(v___x_1753_, v___x_1756_);
            crate::leanh::lean_dec_ref(v___x_1756_);
            return v___x_1757_;
        }
        2 => {
            let mut v_package_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: u8 = 0;
            let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_package_1758_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
            crate::leanh::lean_inc(v_package_1758_);
            v_module_1759_ = crate::leanh::lean_ctor_get(v_x_1746_, 1);
            crate::leanh::lean_inc(v_module_1759_);
            crate::leanh::lean_dec_ref_known(v_x_1746_, 2);
            v___x_1760_ = l_Lean_Name_getPrefix(v_package_1758_);
            crate::leanh::lean_dec(v_package_1758_);
            v___x_1761_ = 1;
            v___x_1762_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_1760_,
                v___x_1761_,
            );
            v___x_1763_ = l_Lake_PartialBuildKey_toString___closed__0;
            v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
            v___x_1765_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_module_1759_,
                v___x_1761_,
            );
            v___x_1766_ = lean_string_append(v___x_1764_, v___x_1765_);
            crate::leanh::lean_dec_ref(v___x_1765_);
            return v___x_1766_;
        }
        3 => {
            let mut v_package_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1770_: u8 = 0;
            let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_package_1767_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
            crate::leanh::lean_inc(v_package_1767_);
            v_target_1768_ = crate::leanh::lean_ctor_get(v_x_1746_, 1);
            crate::leanh::lean_inc(v_target_1768_);
            crate::leanh::lean_dec_ref_known(v_x_1746_, 2);
            v___x_1769_ = l_Lean_Name_getPrefix(v_package_1767_);
            crate::leanh::lean_dec(v_package_1767_);
            v___x_1770_ = 1;
            v___x_1771_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_1769_,
                v___x_1770_,
            );
            v___x_1772_ = l_Lake_PartialBuildKey_toString___closed__1;
            v___x_1773_ = lean_string_append(v___x_1771_, v___x_1772_);
            v___x_1774_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_target_1768_,
                v___x_1770_,
            );
            v___x_1775_ = lean_string_append(v___x_1773_, v___x_1774_);
            crate::leanh::lean_dec_ref(v___x_1774_);
            return v___x_1775_;
        }
        _ => {
            let mut v_target_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1782_: u8 = 0;
            let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_target_1776_ = crate::leanh::lean_ctor_get(v_x_1746_, 0);
            crate::leanh::lean_inc_ref(v_target_1776_);
            v_facet_1777_ = crate::leanh::lean_ctor_get(v_x_1746_, 1);
            crate::leanh::lean_inc(v_facet_1777_);
            crate::leanh::lean_dec_ref_known(v_x_1746_, 2);
            v___x_1778_ = l_Lake_BuildKey_toString(v_target_1776_);
            v___x_1779_ = l_Lake_PartialBuildKey_toString___closed__2;
            v___x_1780_ = lean_string_append(v___x_1778_, v___x_1779_);
            v___x_1781_ = l_Lake_Name_eraseHead(v_facet_1777_);
            v___x_1782_ = 1;
            v___x_1783_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_1781_,
                v___x_1782_,
            );
            v___x_1784_ = lean_string_append(v___x_1780_, v___x_1783_);
            crate::leanh::lean_dec_ref(v___x_1783_);
            return v___x_1784_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_toSimpleString(
    mut v_x_1785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_p_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1785_) {
                0 => {
                    v_module_1796_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    crate::leanh::lean_inc(v_module_1796_);
                    crate::leanh::lean_dec_ref_known(v_x_1785_, 1);
                    v___x_1797_ = 1;
                    v___x_1798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1796_,
                        v___x_1797_,
                    );
                    return v___x_1798_;
                }
                1 => {
                    v_package_1799_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    crate::leanh::lean_inc(v_package_1799_);
                    crate::leanh::lean_dec_ref_known(v_x_1785_, 1);
                    v___x_1800_ = l_Lean_Name_getPrefix(v_package_1799_);
                    crate::leanh::lean_dec(v_package_1799_);
                    v___x_1801_ = 1;
                    v___x_1802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_1800_,
                        v___x_1801_,
                    );
                    return v___x_1802_;
                }
                4 => {
                    v_target_1803_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    crate::leanh::lean_inc_ref(v_target_1803_);
                    v_facet_1804_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    crate::leanh::lean_inc(v_facet_1804_);
                    crate::leanh::lean_dec_ref_known(v_x_1785_, 2);
                    v___x_1805_ = l_Lake_BuildKey_toSimpleString(v_target_1803_);
                    v___x_1806_ = l_Lake_PartialBuildKey_toString___closed__2;
                    v___x_1807_ = lean_string_append(v___x_1805_, v___x_1806_);
                    v___x_1808_ = l_Lake_Name_eraseHead(v_facet_1804_);
                    v___x_1809_ = 1;
                    v___x_1810_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_1808_,
                        v___x_1809_,
                    );
                    v___x_1811_ = lean_string_append(v___x_1807_, v___x_1810_);
                    crate::leanh::lean_dec_ref(v___x_1810_);
                    return v___x_1811_;
                }
                _ => {
                    v_package_1812_ = crate::leanh::lean_ctor_get(v_x_1785_, 0);
                    crate::leanh::lean_inc(v_package_1812_);
                    v_module_1813_ = crate::leanh::lean_ctor_get(v_x_1785_, 1);
                    crate::leanh::lean_inc(v_module_1813_);
                    crate::leanh::lean_dec_ref(v_x_1785_);
                    v_p_1787_ = v_package_1812_;
                    v_m_1788_ = v_module_1813_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1789_ = l_Lean_Name_getPrefix(v_p_1787_);
                crate::leanh::lean_dec(v_p_1787_);
                v___x_1790_ = 1;
                v___x_1791_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_1789_,
                    v___x_1790_,
                );
                v___x_1792_ = l_Lake_PartialBuildKey_toString___closed__1;
                v___x_1793_ = lean_string_append(v___x_1791_, v___x_1792_);
                v___x_1794_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_m_1788_,
                    v___x_1790_,
                );
                v___x_1795_ = lean_string_append(v___x_1793_, v___x_1794_);
                crate::leanh::lean_dec_ref(v___x_1794_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildKey_quickCmp(
    mut v_k_1816_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1817_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_k_1816_) {
        0 => {
            if crate::leanh::lean_obj_tag(v_k_x27_1817_) == 0 {
                let mut v_module_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1820_: u8 = 0;
                v_module_1818_ = crate::leanh::lean_ctor_get(v_k_1816_, 0);
                v_module_1819_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v___x_1820_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                    v_module_1818_,
                    v_module_1819_,
                );
                return v___x_1820_;
            } else {
                let mut v___x_1821_: u8 = 0;
                v___x_1821_ = 0;
                return v___x_1821_;
            }
        }
        1 => match crate::leanh::lean_obj_tag(v_k_x27_1817_) {
            0 => {
                let mut v___x_1822_: u8 = 0;
                v___x_1822_ = 2;
                return v___x_1822_;
            }
            1 => {
                let mut v_package_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1825_: u8 = 0;
                v_package_1823_ = crate::leanh::lean_ctor_get(v_k_1816_, 0);
                v_package_1824_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v___x_1825_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                    v_package_1823_,
                    v_package_1824_,
                );
                return v___x_1825_;
            }
            _ => {
                let mut v___x_1826_: u8 = 0;
                v___x_1826_ = 0;
                return v___x_1826_;
            }
        },
        2 => match crate::leanh::lean_obj_tag(v_k_x27_1817_) {
            4 => {
                let mut v___x_1827_: u8 = 0;
                v___x_1827_ = 0;
                return v___x_1827_;
            }
            3 => {
                let mut v___x_1828_: u8 = 0;
                v___x_1828_ = 0;
                return v___x_1828_;
            }
            2 => {
                let mut v_package_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1833_: u8 = 0;
                v_package_1829_ = crate::leanh::lean_ctor_get(v_k_1816_, 0);
                v_module_1830_ = crate::leanh::lean_ctor_get(v_k_1816_, 1);
                v_package_1831_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_module_1832_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 1);
                v___x_1833_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                    v_module_1830_,
                    v_module_1832_,
                );
                if v___x_1833_ == 1 {
                    let mut v___x_1834_: u8 = 0;
                    v___x_1834_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                        v_package_1829_,
                        v_package_1831_,
                    );
                    return v___x_1834_;
                } else {
                    return v___x_1833_;
                }
            }
            _ => {
                let mut v___x_1835_: u8 = 0;
                v___x_1835_ = 2;
                return v___x_1835_;
            }
        },
        3 => match crate::leanh::lean_obj_tag(v_k_x27_1817_) {
            4 => {
                let mut v___x_1836_: u8 = 0;
                v___x_1836_ = 0;
                return v___x_1836_;
            }
            3 => {
                let mut v_package_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1841_: u8 = 0;
                v_package_1837_ = crate::leanh::lean_ctor_get(v_k_1816_, 0);
                v_target_1838_ = crate::leanh::lean_ctor_get(v_k_1816_, 1);
                v_package_1839_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_target_1840_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 1);
                v___x_1841_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                    v_package_1837_,
                    v_package_1839_,
                );
                if v___x_1841_ == 1 {
                    let mut v___x_1842_: u8 = 0;
                    v___x_1842_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                        v_target_1838_,
                        v_target_1840_,
                    );
                    return v___x_1842_;
                } else {
                    return v___x_1841_;
                }
            }
            _ => {
                let mut v___x_1843_: u8 = 0;
                v___x_1843_ = 2;
                return v___x_1843_;
            }
        },
        _ => {
            if crate::leanh::lean_obj_tag(v_k_x27_1817_) == 4 {
                let mut v_target_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1848_: u8 = 0;
                v_target_1844_ = crate::leanh::lean_ctor_get(v_k_1816_, 0);
                v_facet_1845_ = crate::leanh::lean_ctor_get(v_k_1816_, 1);
                v_target_1846_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_facet_1847_ = crate::leanh::lean_ctor_get(v_k_x27_1817_, 1);
                v___x_1848_ = l_Lake_BuildKey_quickCmp(v_target_1844_, v_target_1846_);
                if v___x_1848_ == 1 {
                    let mut v___x_1849_: u8 = 0;
                    v___x_1849_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(
                        v_facet_1845_,
                        v_facet_1847_,
                    );
                    return v___x_1849_;
                } else {
                    return v___x_1848_;
                }
            } else {
                let mut v___x_1850_: u8 = 0;
                v___x_1850_ = 2;
                return v___x_1850_;
            }
        }
    }
}
pub unsafe fn l_Lake_BuildKey_quickCmp___boxed(
    mut v_k_1851_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1853_: u8 = 0;
    let mut v_r_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1853_ = l_Lake_BuildKey_quickCmp(v_k_1851_, v_k_x27_1852_);
    crate::leanh::lean_dec_ref(v_k_x27_1852_);
    crate::leanh::lean_dec_ref(v_k_1851_);
    v_r_1854_ = crate::leanh::lean_box((v_res_1853_) as usize);
    return v_r_1854_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(
    mut v_x_1855_: *mut crate::leanh::LeanObject,
    mut v_h__1_1856_: *mut crate::leanh::LeanObject,
    mut v_h__2_1857_: *mut crate::leanh::LeanObject,
    mut v_h__3_1858_: *mut crate::leanh::LeanObject,
    mut v_h__4_1859_: *mut crate::leanh::LeanObject,
    mut v_h__5_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1855_) {
        0 => {
            let mut v_module_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1860_);
            crate::leanh::lean_dec(v_h__4_1859_);
            crate::leanh::lean_dec(v_h__3_1858_);
            crate::leanh::lean_dec(v_h__2_1857_);
            v_module_1861_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
            crate::leanh::lean_inc(v_module_1861_);
            crate::leanh::lean_dec_ref_known(v_x_1855_, 1);
            v___x_1862_ = crate::leanh::lean_apply_1(v_h__1_1856_, v_module_1861_);
            return v___x_1862_;
        }
        1 => {
            let mut v_package_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1860_);
            crate::leanh::lean_dec(v_h__4_1859_);
            crate::leanh::lean_dec(v_h__3_1858_);
            crate::leanh::lean_dec(v_h__1_1856_);
            v_package_1863_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
            crate::leanh::lean_inc(v_package_1863_);
            crate::leanh::lean_dec_ref_known(v_x_1855_, 1);
            v___x_1864_ = crate::leanh::lean_apply_1(v_h__2_1857_, v_package_1863_);
            return v___x_1864_;
        }
        2 => {
            let mut v_package_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1860_);
            crate::leanh::lean_dec(v_h__4_1859_);
            crate::leanh::lean_dec(v_h__2_1857_);
            crate::leanh::lean_dec(v_h__1_1856_);
            v_package_1865_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
            crate::leanh::lean_inc(v_package_1865_);
            v_module_1866_ = crate::leanh::lean_ctor_get(v_x_1855_, 1);
            crate::leanh::lean_inc(v_module_1866_);
            crate::leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1867_ = crate::leanh::lean_apply_2(v_h__3_1858_, v_package_1865_, v_module_1866_);
            return v___x_1867_;
        }
        3 => {
            let mut v_package_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1860_);
            crate::leanh::lean_dec(v_h__3_1858_);
            crate::leanh::lean_dec(v_h__2_1857_);
            crate::leanh::lean_dec(v_h__1_1856_);
            v_package_1868_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
            crate::leanh::lean_inc(v_package_1868_);
            v_target_1869_ = crate::leanh::lean_ctor_get(v_x_1855_, 1);
            crate::leanh::lean_inc(v_target_1869_);
            crate::leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1870_ = crate::leanh::lean_apply_2(v_h__4_1859_, v_package_1868_, v_target_1869_);
            return v___x_1870_;
        }
        _ => {
            let mut v_target_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1859_);
            crate::leanh::lean_dec(v_h__3_1858_);
            crate::leanh::lean_dec(v_h__2_1857_);
            crate::leanh::lean_dec(v_h__1_1856_);
            v_target_1871_ = crate::leanh::lean_ctor_get(v_x_1855_, 0);
            crate::leanh::lean_inc_ref(v_target_1871_);
            v_facet_1872_ = crate::leanh::lean_ctor_get(v_x_1855_, 1);
            crate::leanh::lean_inc(v_facet_1872_);
            crate::leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1873_ = crate::leanh::lean_apply_2(v_h__5_1860_, v_target_1871_, v_facet_1872_);
            return v___x_1873_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(
    mut v_motive_1874_: *mut crate::leanh::LeanObject,
    mut v_x_1875_: *mut crate::leanh::LeanObject,
    mut v_h__1_1876_: *mut crate::leanh::LeanObject,
    mut v_h__2_1877_: *mut crate::leanh::LeanObject,
    mut v_h__3_1878_: *mut crate::leanh::LeanObject,
    mut v_h__4_1879_: *mut crate::leanh::LeanObject,
    mut v_h__5_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1875_) {
        0 => {
            let mut v_module_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1880_);
            crate::leanh::lean_dec(v_h__4_1879_);
            crate::leanh::lean_dec(v_h__3_1878_);
            crate::leanh::lean_dec(v_h__2_1877_);
            v_module_1881_ = crate::leanh::lean_ctor_get(v_x_1875_, 0);
            crate::leanh::lean_inc(v_module_1881_);
            crate::leanh::lean_dec_ref_known(v_x_1875_, 1);
            v___x_1882_ = crate::leanh::lean_apply_1(v_h__1_1876_, v_module_1881_);
            return v___x_1882_;
        }
        1 => {
            let mut v_package_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1880_);
            crate::leanh::lean_dec(v_h__4_1879_);
            crate::leanh::lean_dec(v_h__3_1878_);
            crate::leanh::lean_dec(v_h__1_1876_);
            v_package_1883_ = crate::leanh::lean_ctor_get(v_x_1875_, 0);
            crate::leanh::lean_inc(v_package_1883_);
            crate::leanh::lean_dec_ref_known(v_x_1875_, 1);
            v___x_1884_ = crate::leanh::lean_apply_1(v_h__2_1877_, v_package_1883_);
            return v___x_1884_;
        }
        2 => {
            let mut v_package_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1880_);
            crate::leanh::lean_dec(v_h__4_1879_);
            crate::leanh::lean_dec(v_h__2_1877_);
            crate::leanh::lean_dec(v_h__1_1876_);
            v_package_1885_ = crate::leanh::lean_ctor_get(v_x_1875_, 0);
            crate::leanh::lean_inc(v_package_1885_);
            v_module_1886_ = crate::leanh::lean_ctor_get(v_x_1875_, 1);
            crate::leanh::lean_inc(v_module_1886_);
            crate::leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1887_ = crate::leanh::lean_apply_2(v_h__3_1878_, v_package_1885_, v_module_1886_);
            return v___x_1887_;
        }
        3 => {
            let mut v_package_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1880_);
            crate::leanh::lean_dec(v_h__3_1878_);
            crate::leanh::lean_dec(v_h__2_1877_);
            crate::leanh::lean_dec(v_h__1_1876_);
            v_package_1888_ = crate::leanh::lean_ctor_get(v_x_1875_, 0);
            crate::leanh::lean_inc(v_package_1888_);
            v_target_1889_ = crate::leanh::lean_ctor_get(v_x_1875_, 1);
            crate::leanh::lean_inc(v_target_1889_);
            crate::leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1890_ = crate::leanh::lean_apply_2(v_h__4_1879_, v_package_1888_, v_target_1889_);
            return v___x_1890_;
        }
        _ => {
            let mut v_target_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1879_);
            crate::leanh::lean_dec(v_h__3_1878_);
            crate::leanh::lean_dec(v_h__2_1877_);
            crate::leanh::lean_dec(v_h__1_1876_);
            v_target_1891_ = crate::leanh::lean_ctor_get(v_x_1875_, 0);
            crate::leanh::lean_inc_ref(v_target_1891_);
            v_facet_1892_ = crate::leanh::lean_ctor_get(v_x_1875_, 1);
            crate::leanh::lean_inc(v_facet_1892_);
            crate::leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1893_ = crate::leanh::lean_apply_2(v_h__5_1880_, v_target_1891_, v_facet_1892_);
            return v___x_1893_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(
    mut v_k_x27_1894_: *mut crate::leanh::LeanObject,
    mut v_h__1_1895_: *mut crate::leanh::LeanObject,
    mut v_h__2_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_k_x27_1894_) == 0 {
        let mut v_module_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1896_);
        v_module_1897_ = crate::leanh::lean_ctor_get(v_k_x27_1894_, 0);
        crate::leanh::lean_inc(v_module_1897_);
        crate::leanh::lean_dec_ref_known(v_k_x27_1894_, 1);
        v___x_1898_ = crate::leanh::lean_apply_1(v_h__1_1895_, v_module_1897_);
        return v___x_1898_;
    } else {
        let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1895_);
        v___x_1899_ =
            crate::leanh::lean_apply_2(v_h__2_1896_, v_k_x27_1894_, crate::leanh::lean_box(0));
        return v___x_1899_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(
    mut v_motive_1900_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1901_: *mut crate::leanh::LeanObject,
    mut v_h__1_1902_: *mut crate::leanh::LeanObject,
    mut v_h__2_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_k_x27_1901_) == 0 {
        let mut v_module_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1903_);
        v_module_1904_ = crate::leanh::lean_ctor_get(v_k_x27_1901_, 0);
        crate::leanh::lean_inc(v_module_1904_);
        crate::leanh::lean_dec_ref_known(v_k_x27_1901_, 1);
        v___x_1905_ = crate::leanh::lean_apply_1(v_h__1_1902_, v_module_1904_);
        return v___x_1905_;
    } else {
        let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1902_);
        v___x_1906_ =
            crate::leanh::lean_apply_2(v_h__2_1903_, v_k_x27_1901_, crate::leanh::lean_box(0));
        return v___x_1906_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(
    mut v_k_x27_1907_: *mut crate::leanh::LeanObject,
    mut v_h__1_1908_: *mut crate::leanh::LeanObject,
    mut v_h__2_1909_: *mut crate::leanh::LeanObject,
    mut v_h__3_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1907_) {
        0 => {
            let mut v_module_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1910_);
            crate::leanh::lean_dec(v_h__2_1909_);
            v_module_1911_ = crate::leanh::lean_ctor_get(v_k_x27_1907_, 0);
            crate::leanh::lean_inc(v_module_1911_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1907_, 1);
            v___x_1912_ = crate::leanh::lean_apply_1(v_h__1_1908_, v_module_1911_);
            return v___x_1912_;
        }
        1 => {
            let mut v_package_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1910_);
            crate::leanh::lean_dec(v_h__1_1908_);
            v_package_1913_ = crate::leanh::lean_ctor_get(v_k_x27_1907_, 0);
            crate::leanh::lean_inc(v_package_1913_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1907_, 1);
            v___x_1914_ = crate::leanh::lean_apply_1(v_h__2_1909_, v_package_1913_);
            return v___x_1914_;
        }
        _ => {
            let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1909_);
            crate::leanh::lean_dec(v_h__1_1908_);
            v___x_1915_ = crate::leanh::lean_apply_3(
                v_h__3_1910_,
                v_k_x27_1907_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1915_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(
    mut v_motive_1916_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1917_: *mut crate::leanh::LeanObject,
    mut v_h__1_1918_: *mut crate::leanh::LeanObject,
    mut v_h__2_1919_: *mut crate::leanh::LeanObject,
    mut v_h__3_1920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1917_) {
        0 => {
            let mut v_module_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1920_);
            crate::leanh::lean_dec(v_h__2_1919_);
            v_module_1921_ = crate::leanh::lean_ctor_get(v_k_x27_1917_, 0);
            crate::leanh::lean_inc(v_module_1921_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1917_, 1);
            v___x_1922_ = crate::leanh::lean_apply_1(v_h__1_1918_, v_module_1921_);
            return v___x_1922_;
        }
        1 => {
            let mut v_package_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1920_);
            crate::leanh::lean_dec(v_h__1_1918_);
            v_package_1923_ = crate::leanh::lean_ctor_get(v_k_x27_1917_, 0);
            crate::leanh::lean_inc(v_package_1923_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1917_, 1);
            v___x_1924_ = crate::leanh::lean_apply_1(v_h__2_1919_, v_package_1923_);
            return v___x_1924_;
        }
        _ => {
            let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1919_);
            crate::leanh::lean_dec(v_h__1_1918_);
            v___x_1925_ = crate::leanh::lean_apply_3(
                v_h__3_1920_,
                v_k_x27_1917_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1925_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(
    mut v_k_x27_1926_: *mut crate::leanh::LeanObject,
    mut v_h__1_1927_: *mut crate::leanh::LeanObject,
    mut v_h__2_1928_: *mut crate::leanh::LeanObject,
    mut v_h__3_1929_: *mut crate::leanh::LeanObject,
    mut v_h__4_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1926_) {
        4 => {
            let mut v_target_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1930_);
            crate::leanh::lean_dec(v_h__3_1929_);
            crate::leanh::lean_dec(v_h__2_1928_);
            v_target_1931_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 0);
            crate::leanh::lean_inc_ref(v_target_1931_);
            v_facet_1932_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 1);
            crate::leanh::lean_inc(v_facet_1932_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1933_ = crate::leanh::lean_apply_2(v_h__1_1927_, v_target_1931_, v_facet_1932_);
            return v___x_1933_;
        }
        3 => {
            let mut v_package_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1930_);
            crate::leanh::lean_dec(v_h__3_1929_);
            crate::leanh::lean_dec(v_h__1_1927_);
            v_package_1934_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 0);
            crate::leanh::lean_inc(v_package_1934_);
            v_target_1935_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 1);
            crate::leanh::lean_inc(v_target_1935_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1936_ = crate::leanh::lean_apply_2(v_h__2_1928_, v_package_1934_, v_target_1935_);
            return v___x_1936_;
        }
        2 => {
            let mut v_package_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1930_);
            crate::leanh::lean_dec(v_h__2_1928_);
            crate::leanh::lean_dec(v_h__1_1927_);
            v_package_1937_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 0);
            crate::leanh::lean_inc(v_package_1937_);
            v_module_1938_ = crate::leanh::lean_ctor_get(v_k_x27_1926_, 1);
            crate::leanh::lean_inc(v_module_1938_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1939_ = crate::leanh::lean_apply_2(v_h__3_1929_, v_package_1937_, v_module_1938_);
            return v___x_1939_;
        }
        _ => {
            let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1929_);
            crate::leanh::lean_dec(v_h__2_1928_);
            crate::leanh::lean_dec(v_h__1_1927_);
            v___x_1940_ = crate::leanh::lean_apply_4(
                v_h__4_1930_,
                v_k_x27_1926_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1940_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(
    mut v_motive_1941_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1942_: *mut crate::leanh::LeanObject,
    mut v_h__1_1943_: *mut crate::leanh::LeanObject,
    mut v_h__2_1944_: *mut crate::leanh::LeanObject,
    mut v_h__3_1945_: *mut crate::leanh::LeanObject,
    mut v_h__4_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1942_) {
        4 => {
            let mut v_target_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1946_);
            crate::leanh::lean_dec(v_h__3_1945_);
            crate::leanh::lean_dec(v_h__2_1944_);
            v_target_1947_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 0);
            crate::leanh::lean_inc_ref(v_target_1947_);
            v_facet_1948_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 1);
            crate::leanh::lean_inc(v_facet_1948_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1949_ = crate::leanh::lean_apply_2(v_h__1_1943_, v_target_1947_, v_facet_1948_);
            return v___x_1949_;
        }
        3 => {
            let mut v_package_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1946_);
            crate::leanh::lean_dec(v_h__3_1945_);
            crate::leanh::lean_dec(v_h__1_1943_);
            v_package_1950_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 0);
            crate::leanh::lean_inc(v_package_1950_);
            v_target_1951_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 1);
            crate::leanh::lean_inc(v_target_1951_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1952_ = crate::leanh::lean_apply_2(v_h__2_1944_, v_package_1950_, v_target_1951_);
            return v___x_1952_;
        }
        2 => {
            let mut v_package_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1946_);
            crate::leanh::lean_dec(v_h__2_1944_);
            crate::leanh::lean_dec(v_h__1_1943_);
            v_package_1953_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 0);
            crate::leanh::lean_inc(v_package_1953_);
            v_module_1954_ = crate::leanh::lean_ctor_get(v_k_x27_1942_, 1);
            crate::leanh::lean_inc(v_module_1954_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1955_ = crate::leanh::lean_apply_2(v_h__3_1945_, v_package_1953_, v_module_1954_);
            return v___x_1955_;
        }
        _ => {
            let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1945_);
            crate::leanh::lean_dec(v_h__2_1944_);
            crate::leanh::lean_dec(v_h__1_1943_);
            v___x_1956_ = crate::leanh::lean_apply_4(
                v_h__4_1946_,
                v_k_x27_1942_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1956_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(
    mut v_x_1957_: u8,
    mut v_h__1_1958_: *mut crate::leanh::LeanObject,
    mut v_h__2_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1957_ == 1 {
        let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1959_);
        v___x_1960_ = crate::leanh::lean_box(0);
        v___x_1961_ = crate::leanh::lean_apply_1(v_h__1_1958_, v___x_1960_);
        return v___x_1961_;
    } else {
        let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1958_);
        v___x_1962_ = crate::leanh::lean_box((v_x_1957_) as usize);
        v___x_1963_ =
            crate::leanh::lean_apply_2(v_h__2_1959_, v___x_1962_, crate::leanh::lean_box(0));
        return v___x_1963_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(
    mut v_x_1964_: *mut crate::leanh::LeanObject,
    mut v_h__1_1965_: *mut crate::leanh::LeanObject,
    mut v_h__2_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1967_: u8 = 0;
    let mut v_res_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1967_ = (crate::leanh::lean_unbox(v_x_1964_) as u8);
    v_res_1968_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(
        v_x_17__boxed_1967_,
        v_h__1_1965_,
        v_h__2_1966_,
    );
    return v_res_1968_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(
    mut v_motive_1969_: *mut crate::leanh::LeanObject,
    mut v_x_1970_: u8,
    mut v_h__1_1971_: *mut crate::leanh::LeanObject,
    mut v_h__2_1972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1970_ == 1 {
        let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1972_);
        v___x_1973_ = crate::leanh::lean_box(0);
        v___x_1974_ = crate::leanh::lean_apply_1(v_h__1_1971_, v___x_1973_);
        return v___x_1974_;
    } else {
        let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1971_);
        v___x_1975_ = crate::leanh::lean_box((v_x_1970_) as usize);
        v___x_1976_ =
            crate::leanh::lean_apply_2(v_h__2_1972_, v___x_1975_, crate::leanh::lean_box(0));
        return v___x_1976_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(
    mut v_motive_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: *mut crate::leanh::LeanObject,
    mut v_h__1_1979_: *mut crate::leanh::LeanObject,
    mut v_h__2_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28__boxed_1981_: u8 = 0;
    let mut v_res_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_1981_ = (crate::leanh::lean_unbox(v_x_1978_) as u8);
    v_res_1982_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(
        v_motive_1977_,
        v_x_28__boxed_1981_,
        v_h__1_1979_,
        v_h__2_1980_,
    );
    return v_res_1982_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(
    mut v_k_x27_1983_: *mut crate::leanh::LeanObject,
    mut v_h__1_1984_: *mut crate::leanh::LeanObject,
    mut v_h__2_1985_: *mut crate::leanh::LeanObject,
    mut v_h__3_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1983_) {
        4 => {
            let mut v_target_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1986_);
            crate::leanh::lean_dec(v_h__2_1985_);
            v_target_1987_ = crate::leanh::lean_ctor_get(v_k_x27_1983_, 0);
            crate::leanh::lean_inc_ref(v_target_1987_);
            v_facet_1988_ = crate::leanh::lean_ctor_get(v_k_x27_1983_, 1);
            crate::leanh::lean_inc(v_facet_1988_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1983_, 2);
            v___x_1989_ = crate::leanh::lean_apply_2(v_h__1_1984_, v_target_1987_, v_facet_1988_);
            return v___x_1989_;
        }
        3 => {
            let mut v_package_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1986_);
            crate::leanh::lean_dec(v_h__1_1984_);
            v_package_1990_ = crate::leanh::lean_ctor_get(v_k_x27_1983_, 0);
            crate::leanh::lean_inc(v_package_1990_);
            v_target_1991_ = crate::leanh::lean_ctor_get(v_k_x27_1983_, 1);
            crate::leanh::lean_inc(v_target_1991_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1983_, 2);
            v___x_1992_ = crate::leanh::lean_apply_2(v_h__2_1985_, v_package_1990_, v_target_1991_);
            return v___x_1992_;
        }
        _ => {
            let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1985_);
            crate::leanh::lean_dec(v_h__1_1984_);
            v___x_1993_ = crate::leanh::lean_apply_3(
                v_h__3_1986_,
                v_k_x27_1983_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1993_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(
    mut v_motive_1994_: *mut crate::leanh::LeanObject,
    mut v_k_x27_1995_: *mut crate::leanh::LeanObject,
    mut v_h__1_1996_: *mut crate::leanh::LeanObject,
    mut v_h__2_1997_: *mut crate::leanh::LeanObject,
    mut v_h__3_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_k_x27_1995_) {
        4 => {
            let mut v_target_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1998_);
            crate::leanh::lean_dec(v_h__2_1997_);
            v_target_1999_ = crate::leanh::lean_ctor_get(v_k_x27_1995_, 0);
            crate::leanh::lean_inc_ref(v_target_1999_);
            v_facet_2000_ = crate::leanh::lean_ctor_get(v_k_x27_1995_, 1);
            crate::leanh::lean_inc(v_facet_2000_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1995_, 2);
            v___x_2001_ = crate::leanh::lean_apply_2(v_h__1_1996_, v_target_1999_, v_facet_2000_);
            return v___x_2001_;
        }
        3 => {
            let mut v_package_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1998_);
            crate::leanh::lean_dec(v_h__1_1996_);
            v_package_2002_ = crate::leanh::lean_ctor_get(v_k_x27_1995_, 0);
            crate::leanh::lean_inc(v_package_2002_);
            v_target_2003_ = crate::leanh::lean_ctor_get(v_k_x27_1995_, 1);
            crate::leanh::lean_inc(v_target_2003_);
            crate::leanh::lean_dec_ref_known(v_k_x27_1995_, 2);
            v___x_2004_ = crate::leanh::lean_apply_2(v_h__2_1997_, v_package_2002_, v_target_2003_);
            return v___x_2004_;
        }
        _ => {
            let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1997_);
            crate::leanh::lean_dec(v_h__1_1996_);
            v___x_2005_ = crate::leanh::lean_apply_3(
                v_h__3_1998_,
                v_k_x27_1995_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_2005_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(
    mut v_k_x27_2006_: *mut crate::leanh::LeanObject,
    mut v_h__1_2007_: *mut crate::leanh::LeanObject,
    mut v_h__2_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_k_x27_2006_) == 4 {
        let mut v_target_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_facet_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2008_);
        v_target_2009_ = crate::leanh::lean_ctor_get(v_k_x27_2006_, 0);
        crate::leanh::lean_inc_ref(v_target_2009_);
        v_facet_2010_ = crate::leanh::lean_ctor_get(v_k_x27_2006_, 1);
        crate::leanh::lean_inc(v_facet_2010_);
        crate::leanh::lean_dec_ref_known(v_k_x27_2006_, 2);
        v___x_2011_ = crate::leanh::lean_apply_2(v_h__1_2007_, v_target_2009_, v_facet_2010_);
        return v___x_2011_;
    } else {
        let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2007_);
        v___x_2012_ =
            crate::leanh::lean_apply_2(v_h__2_2008_, v_k_x27_2006_, crate::leanh::lean_box(0));
        return v___x_2012_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(
    mut v_motive_2013_: *mut crate::leanh::LeanObject,
    mut v_k_x27_2014_: *mut crate::leanh::LeanObject,
    mut v_h__1_2015_: *mut crate::leanh::LeanObject,
    mut v_h__2_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_k_x27_2014_) == 4 {
        let mut v_target_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_facet_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_2016_);
        v_target_2017_ = crate::leanh::lean_ctor_get(v_k_x27_2014_, 0);
        crate::leanh::lean_inc_ref(v_target_2017_);
        v_facet_2018_ = crate::leanh::lean_ctor_get(v_k_x27_2014_, 1);
        crate::leanh::lean_inc(v_facet_2018_);
        crate::leanh::lean_dec_ref_known(v_k_x27_2014_, 2);
        v___x_2019_ = crate::leanh::lean_apply_2(v_h__1_2015_, v_target_2017_, v_facet_2018_);
        return v___x_2019_;
    } else {
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_2015_);
        v___x_2020_ =
            crate::leanh::lean_apply_2(v_h__2_2016_, v_k_x27_2014_, crate::leanh::lean_box(0));
        return v___x_2020_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Key(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Key(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Key(builtin);
}
