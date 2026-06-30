// Lean compiler output
// Module: Lake.Build.Key
// Imports: Init.Data.Order Lake.Util.Name Init.Data.String.Search Init.Data.Iterators.Consumers
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_string_append,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast, lean_uint32_dec_eq,
    lean_uint64_mix_hash, lean_uint64_of_nat,
};
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
pub static l_Lake_instInhabitedBuildKey_default___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_instInhabitedBuildKey_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedBuildKey_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instInhabitedBuildKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instInhabitedBuildKey_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__0_value: leanh::LeanStringObject<21> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 109, 111, 100, 117,
            108, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__2_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lake_instReprBuildKey_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildKey_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_instReprBuildKey_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instReprBuildKey_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_instReprBuildKey_repr___closed__5_value: leanh::LeanStringObject<22> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 112, 97, 99, 107, 97,
            103, 101, 0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__7_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__8_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildKey_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__10_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__9_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__11_value: leanh::LeanStringObject<28> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_instReprBuildKey_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__12_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__13_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__12_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__14_value: leanh::LeanStringObject<20> =
    leanh::LeanStringObject {
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 75, 101, 121, 46, 102, 97, 99, 101, 116,
            0,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__15_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey_repr___closed__16_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__15_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_instReprBuildKey_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey_repr___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lake_instReprBuildKey___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instReprBuildKey_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instReprBuildKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lake_instReprBuildKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instReprBuildKey___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lake_instHashableBuildKey_hash___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__0: u64 = 0;
static mut l_Lake_instHashableBuildKey_hash___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__1: u64 = 0;
static mut l_Lake_instHashableBuildKey_hash___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_instHashableBuildKey_hash___closed__2: u64 = 0;
pub static l_Lake_instHashableBuildKey___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_instHashableBuildKey_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instHashableBuildKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableBuildKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instHashableBuildKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instHashableBuildKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value:
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
    m_fun: l_Lake_PartialBuildKey_mk___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instCoeBuildKey___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instCoeBuildKey: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instCoeBuildKey___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value:
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
    m_fun: l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instRepr___private__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instRepr___private__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instRepr___private__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instInhabited___closed__0_value: leanh::LeanCtorObject<1> =
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
static mut l_Lake_PartialBuildKey_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instInhabited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [43, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value: leanh::LeanStringObject<83> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 83, m_capacity: 83, m_length: 82, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 100, 101, 102, 97, 117, 108, 116, 32, 112, 97, 99, 107, 97, 103, 101, 32, 116, 97, 114, 103, 101, 116, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 105, 110, 32, 112, 97, 114, 116, 105, 97, 108, 32, 98, 117, 105, 108, 100, 32, 107, 101, 121, 115, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__2_value) as *mut leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__3_value) as *mut leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value: leanh::LeanStringObject<32> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 116, 111, 111, 32, 109, 97, 110, 121, 32, 39, 47, 39, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value: leanh::LeanStringObject<50> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 116, 97, 114, 103, 101, 116, 58, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 32, 110, 97, 109, 101, 32, 97, 102, 116, 101, 114, 32, 39, 43, 39, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__3_value) as *mut leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_PartialBuildKey_instInhabited___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [64, 0]};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value:
    leanh::LeanStringObject<1> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__0_value: leanh::LeanArrayObject<0> =
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
static mut l_Lake_PartialBuildKey_parse___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__1_value: leanh::LeanStringObject<15> =
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
            76, 97, 107, 101, 46, 66, 117, 105, 108, 100, 46, 75, 101, 121, 0,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__2_value: leanh::LeanStringObject<27> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_PartialBuildKey_parse___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__3_value: leanh::LeanStringObject<34> =
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
static mut l_Lake_PartialBuildKey_parse___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lake_PartialBuildKey_parse___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_PartialBuildKey_parse___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_PartialBuildKey_parse___closed__5_value: leanh::LeanStringObject<32> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_PartialBuildKey_parse___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_parse___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_PartialBuildKey_parse___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_parse___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [47, 43, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [47, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_toString___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [58, 0],
    };
static mut l_Lake_PartialBuildKey_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_toString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_PartialBuildKey_instToString___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_PartialBuildKey_toString as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_PartialBuildKey_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_PartialBuildKey_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_PartialBuildKey_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_BuildKey_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_BuildKey_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_BuildKey_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildKey_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_BuildKey_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_BuildKey_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_BuildKey_ctorIdx(
    mut v_x_1011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1011_) {
        0 => {
            let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1012_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1012_;
        }
        1 => {
            let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1013_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1013_;
        }
        2 => {
            let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1014_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1014_;
        }
        3 => {
            let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1015_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1015_;
        }
        _ => {
            let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1016_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1016_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_ctorIdx___boxed(
    mut v_x_1017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Lake_BuildKey_ctorIdx(v_x_1017_);
    leanh::lean_dec_ref(v_x_1017_);
    return v_res_1018_;
}
pub unsafe fn l_Lake_BuildKey_ctorElim___redArg(
    mut v_t_1019_: *mut leanh::LeanObject,
    mut v_k_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1019_) {
        2 => {
            let mut v_package_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_package_1021_ = leanh::lean_ctor_get(v_t_1019_, 0);
            leanh::lean_inc(v_package_1021_);
            v_module_1022_ = leanh::lean_ctor_get(v_t_1019_, 1);
            leanh::lean_inc(v_module_1022_);
            leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1023_ = leanh::lean_apply_2(v_k_1020_, v_package_1021_, v_module_1022_);
            return v___x_1023_;
        }
        3 => {
            let mut v_package_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_package_1024_ = leanh::lean_ctor_get(v_t_1019_, 0);
            leanh::lean_inc(v_package_1024_);
            v_target_1025_ = leanh::lean_ctor_get(v_t_1019_, 1);
            leanh::lean_inc(v_target_1025_);
            leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1026_ = leanh::lean_apply_2(v_k_1020_, v_package_1024_, v_target_1025_);
            return v___x_1026_;
        }
        4 => {
            let mut v_target_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_target_1027_ = leanh::lean_ctor_get(v_t_1019_, 0);
            leanh::lean_inc_ref(v_target_1027_);
            v_facet_1028_ = leanh::lean_ctor_get(v_t_1019_, 1);
            leanh::lean_inc(v_facet_1028_);
            leanh::lean_dec_ref_known(v_t_1019_, 2);
            v___x_1029_ = leanh::lean_apply_2(v_k_1020_, v_target_1027_, v_facet_1028_);
            return v___x_1029_;
        }
        _ => {
            let mut v_module_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_module_1030_ = leanh::lean_ctor_get(v_t_1019_, 0);
            leanh::lean_inc(v_module_1030_);
            leanh::lean_dec_ref(v_t_1019_);
            v___x_1031_ = leanh::lean_apply_1(v_k_1020_, v_module_1030_);
            return v___x_1031_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_ctorElim(
    mut v_motive_1032_: *mut leanh::LeanObject,
    mut v_ctorIdx_1033_: *mut leanh::LeanObject,
    mut v_t_1034_: *mut leanh::LeanObject,
    mut v_h_1035_: *mut leanh::LeanObject,
    mut v_k_1036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1037_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1034_, v_k_1036_);
    return v___x_1037_;
}
pub unsafe fn l_Lake_BuildKey_ctorElim___boxed(
    mut v_motive_1038_: *mut leanh::LeanObject,
    mut v_ctorIdx_1039_: *mut leanh::LeanObject,
    mut v_t_1040_: *mut leanh::LeanObject,
    mut v_h_1041_: *mut leanh::LeanObject,
    mut v_k_1042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1043_ = l_Lake_BuildKey_ctorElim(
        v_motive_1038_,
        v_ctorIdx_1039_,
        v_t_1040_,
        v_h_1041_,
        v_k_1042_,
    );
    leanh::lean_dec(v_ctorIdx_1039_);
    return v_res_1043_;
}
pub unsafe fn l_Lake_BuildKey_module_elim___redArg(
    mut v_t_1044_: *mut leanh::LeanObject,
    mut v_module_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1044_, v_module_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Lake_BuildKey_module_elim(
    mut v_motive_1047_: *mut leanh::LeanObject,
    mut v_t_1048_: *mut leanh::LeanObject,
    mut v_h_1049_: *mut leanh::LeanObject,
    mut v_module_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1051_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1048_, v_module_1050_);
    return v___x_1051_;
}
pub unsafe fn l_Lake_BuildKey_package_elim___redArg(
    mut v_t_1052_: *mut leanh::LeanObject,
    mut v_package_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1054_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1052_, v_package_1053_);
    return v___x_1054_;
}
pub unsafe fn l_Lake_BuildKey_package_elim(
    mut v_motive_1055_: *mut leanh::LeanObject,
    mut v_t_1056_: *mut leanh::LeanObject,
    mut v_h_1057_: *mut leanh::LeanObject,
    mut v_package_1058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1059_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1056_, v_package_1058_);
    return v___x_1059_;
}
pub unsafe fn l_Lake_BuildKey_packageModule_elim___redArg(
    mut v_t_1060_: *mut leanh::LeanObject,
    mut v_packageModule_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1062_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1060_, v_packageModule_1061_);
    return v___x_1062_;
}
pub unsafe fn l_Lake_BuildKey_packageModule_elim(
    mut v_motive_1063_: *mut leanh::LeanObject,
    mut v_t_1064_: *mut leanh::LeanObject,
    mut v_h_1065_: *mut leanh::LeanObject,
    mut v_packageModule_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1067_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1064_, v_packageModule_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lake_BuildKey_packageTarget_elim___redArg(
    mut v_t_1068_: *mut leanh::LeanObject,
    mut v_packageTarget_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1068_, v_packageTarget_1069_);
    return v___x_1070_;
}
pub unsafe fn l_Lake_BuildKey_packageTarget_elim(
    mut v_motive_1071_: *mut leanh::LeanObject,
    mut v_t_1072_: *mut leanh::LeanObject,
    mut v_h_1073_: *mut leanh::LeanObject,
    mut v_packageTarget_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1072_, v_packageTarget_1074_);
    return v___x_1075_;
}
pub unsafe fn l_Lake_BuildKey_facet_elim___redArg(
    mut v_t_1076_: *mut leanh::LeanObject,
    mut v_facet_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1078_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1076_, v_facet_1077_);
    return v___x_1078_;
}
pub unsafe fn l_Lake_BuildKey_facet_elim(
    mut v_motive_1079_: *mut leanh::LeanObject,
    mut v_t_1080_: *mut leanh::LeanObject,
    mut v_h_1081_: *mut leanh::LeanObject,
    mut v_facet_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lake_BuildKey_ctorElim___redArg(v_t_1080_, v_facet_1082_);
    return v___x_1083_;
}
pub unsafe fn _init_l_Lake_instReprBuildKey_repr___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1094_ = leanh::lean_unsigned_to_nat(2);
    v___x_1095_ = lean_nat_to_int(v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn _init_l_Lake_instReprBuildKey_repr___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1096_ = leanh::lean_unsigned_to_nat(1);
    v___x_1097_ = lean_nat_to_int(v___x_1096_);
    return v___x_1097_;
}
pub unsafe fn l_Lake_instReprBuildKey_repr(
    mut v_x_1122_: *mut leanh::LeanObject,
    mut v_prec_1123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_module_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: u8 = 0;
    let mut v___x_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1158_: u8 = 0;
    let mut v___y_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: u8 = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1179_: u8 = 0;
    let mut v_package_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1184_: u8 = 0;
    let mut v___y_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: u8 = 0;
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u8 = 0;
    let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1205_: u8 = 0;
    let mut v_target_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1210_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: u8 = 0;
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1122_) {
                0 => {
                    v_module_1124_ = leanh::lean_ctor_get(v_x_1122_, 0);
                    leanh::lean_inc(v_module_1124_);
                    leanh::lean_dec_ref_known(v_x_1122_, 1);
                    v___x_1135_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1136_ = lean_nat_dec_le(v___x_1135_, v_prec_1123_);
                    if v___x_1136_ == 0 {
                        v___x_1137_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__3,
                        );
                        v___y_1126_ = v___x_1137_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1138_ = leanh::lean_obj_once(
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
                    v_package_1139_ = leanh::lean_ctor_get(v_x_1122_, 0);
                    leanh::lean_inc(v_package_1139_);
                    leanh::lean_dec_ref_known(v_x_1122_, 1);
                    v___x_1150_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1151_ = lean_nat_dec_le(v___x_1150_, v_prec_1123_);
                    if v___x_1151_ == 0 {
                        v___x_1152_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                            _init_l_Lake_instReprBuildKey_repr___closed__3,
                        );
                        v___y_1141_ = v___x_1152_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1153_ = leanh::lean_obj_once(
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
                    v_package_1154_ = leanh::lean_ctor_get(v_x_1122_, 0);
                    v_module_1155_ = leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1179_ = (!leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1179_ == 0 {
                        v___x_1157_ = v_x_1122_;
                        v_isShared_1158_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_module_1155_);
                        leanh::lean_inc(v_package_1154_);
                        leanh::lean_dec(v_x_1122_);
                        v___x_1157_ = leanh::lean_box(0);
                        v_isShared_1158_ = v_isSharedCheck_1179_;
                        state = 3;
                        continue;
                    }
                }
                3 => {
                    v_package_1180_ = leanh::lean_ctor_get(v_x_1122_, 0);
                    v_target_1181_ = leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1205_ = (!leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1205_ == 0 {
                        v___x_1183_ = v_x_1122_;
                        v_isShared_1184_ = v_isSharedCheck_1205_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_target_1181_);
                        leanh::lean_inc(v_package_1180_);
                        leanh::lean_dec(v_x_1122_);
                        v___x_1183_ = leanh::lean_box(0);
                        v_isShared_1184_ = v_isSharedCheck_1205_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    v_target_1206_ = leanh::lean_ctor_get(v_x_1122_, 0);
                    v_facet_1207_ = leanh::lean_ctor_get(v_x_1122_, 1);
                    v_isSharedCheck_1230_ = (!leanh::lean_is_exclusive(v_x_1122_)) as u8;
                    if v_isSharedCheck_1230_ == 0 {
                        v___x_1209_ = v_x_1122_;
                        v_isShared_1210_ = v_isSharedCheck_1230_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_facet_1207_);
                        leanh::lean_inc(v_target_1206_);
                        leanh::lean_dec(v_x_1122_);
                        v___x_1209_ = leanh::lean_box(0);
                        v_isShared_1210_ = v_isSharedCheck_1230_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1127_ = l_Lake_instReprBuildKey_repr___closed__2;
                v___x_1128_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1129_ = l_Lean_Name_reprPrec(v_module_1124_, v___x_1128_);
                v___x_1130_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1130_, 0, v___x_1127_);
                leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
                leanh::lean_inc(v___y_1126_);
                v___x_1131_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1131_, 0, v___y_1126_);
                leanh::lean_ctor_set(v___x_1131_, 1, v___x_1130_);
                v___x_1132_ = 0;
                v___x_1133_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1133_, 0, v___x_1131_);
                leanh::lean_ctor_set_uint8(
                    v___x_1133_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1132_,
                );
                v___x_1134_ = l_Repr_addAppParen(v___x_1133_, v_prec_1123_);
                return v___x_1134_;
            }
            2 => {
                v___x_1142_ = l_Lake_instReprBuildKey_repr___closed__7;
                v___x_1143_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1144_ = l_Lean_Name_reprPrec(v_package_1139_, v___x_1143_);
                v___x_1145_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1145_, 0, v___x_1142_);
                leanh::lean_ctor_set(v___x_1145_, 1, v___x_1144_);
                leanh::lean_inc(v___y_1141_);
                v___x_1146_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1146_, 0, v___y_1141_);
                leanh::lean_ctor_set(v___x_1146_, 1, v___x_1145_);
                v___x_1147_ = 0;
                v___x_1148_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1148_, 0, v___x_1146_);
                leanh::lean_ctor_set_uint8(
                    v___x_1148_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1147_,
                );
                v___x_1149_ = l_Repr_addAppParen(v___x_1148_, v_prec_1123_);
                return v___x_1149_;
            }
            3 => {
                v___x_1175_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1176_ = lean_nat_dec_le(v___x_1175_, v_prec_1123_);
                if v___x_1176_ == 0 {
                    v___x_1177_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1160_ = v___x_1177_;
                    state = 4;
                    continue;
                } else {
                    v___x_1178_ = leanh::lean_obj_once(
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
                v___x_1161_ = leanh::lean_box(1);
                v___x_1162_ = l_Lake_instReprBuildKey_repr___closed__10;
                v___x_1163_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1164_ = l_Lean_Name_reprPrec(v_package_1154_, v___x_1163_);
                if v_isShared_1158_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1157_, 5);
                    leanh::lean_ctor_set(v___x_1157_, 1, v___x_1164_);
                    leanh::lean_ctor_set(v___x_1157_, 0, v___x_1162_);
                    v___x_1166_ = v___x_1157_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1162_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1174_, 1, v___x_1164_);
                    v___x_1166_ = v_reuseFailAlloc_1174_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1167_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1167_, 0, v___x_1166_);
                leanh::lean_ctor_set(v___x_1167_, 1, v___x_1161_);
                v___x_1168_ = l_Lean_Name_reprPrec(v_module_1155_, v___x_1163_);
                v___x_1169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1169_, 0, v___x_1167_);
                leanh::lean_ctor_set(v___x_1169_, 1, v___x_1168_);
                leanh::lean_inc(v___y_1160_);
                v___x_1170_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1170_, 0, v___y_1160_);
                leanh::lean_ctor_set(v___x_1170_, 1, v___x_1169_);
                v___x_1171_ = 0;
                v___x_1172_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1172_, 0, v___x_1170_);
                leanh::lean_ctor_set_uint8(
                    v___x_1172_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1171_,
                );
                v___x_1173_ = l_Repr_addAppParen(v___x_1172_, v_prec_1123_);
                return v___x_1173_;
            }
            6 => {
                v___x_1201_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1202_ = lean_nat_dec_le(v___x_1201_, v_prec_1123_);
                if v___x_1202_ == 0 {
                    v___x_1203_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1186_ = v___x_1203_;
                    state = 7;
                    continue;
                } else {
                    v___x_1204_ = leanh::lean_obj_once(
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
                v___x_1187_ = leanh::lean_box(1);
                v___x_1188_ = l_Lake_instReprBuildKey_repr___closed__13;
                v___x_1189_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1190_ = l_Lean_Name_reprPrec(v_package_1180_, v___x_1189_);
                if v_isShared_1184_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1183_, 5);
                    leanh::lean_ctor_set(v___x_1183_, 1, v___x_1190_);
                    leanh::lean_ctor_set(v___x_1183_, 0, v___x_1188_);
                    v___x_1192_ = v___x_1183_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1200_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1200_, 1, v___x_1190_);
                    v___x_1192_ = v_reuseFailAlloc_1200_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1193_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1193_, 0, v___x_1192_);
                leanh::lean_ctor_set(v___x_1193_, 1, v___x_1187_);
                v___x_1194_ = l_Lean_Name_reprPrec(v_target_1181_, v___x_1189_);
                v___x_1195_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1195_, 0, v___x_1193_);
                leanh::lean_ctor_set(v___x_1195_, 1, v___x_1194_);
                leanh::lean_inc(v___y_1186_);
                v___x_1196_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1196_, 0, v___y_1186_);
                leanh::lean_ctor_set(v___x_1196_, 1, v___x_1195_);
                v___x_1197_ = 0;
                v___x_1198_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1198_, 0, v___x_1196_);
                leanh::lean_ctor_set_uint8(
                    v___x_1198_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1197_,
                );
                v___x_1199_ = l_Repr_addAppParen(v___x_1198_, v_prec_1123_);
                return v___x_1199_;
            }
            9 => {
                v___x_1211_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1227_ = lean_nat_dec_le(v___x_1211_, v_prec_1123_);
                if v___x_1227_ == 0 {
                    v___x_1228_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lake_instReprBuildKey_repr___closed__3_once),
                        _init_l_Lake_instReprBuildKey_repr___closed__3,
                    );
                    v___y_1213_ = v___x_1228_;
                    state = 10;
                    continue;
                } else {
                    v___x_1229_ = leanh::lean_obj_once(
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
                v___x_1214_ = leanh::lean_box(1);
                v___x_1215_ = l_Lake_instReprBuildKey_repr___closed__16;
                v___x_1216_ = l_Lake_instReprBuildKey_repr(v_target_1206_, v___x_1211_);
                if v_isShared_1210_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1209_, 5);
                    leanh::lean_ctor_set(v___x_1209_, 1, v___x_1216_);
                    leanh::lean_ctor_set(v___x_1209_, 0, v___x_1215_);
                    v___x_1218_ = v___x_1209_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1215_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1226_, 1, v___x_1216_);
                    v___x_1218_ = v_reuseFailAlloc_1226_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1219_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1219_, 0, v___x_1218_);
                leanh::lean_ctor_set(v___x_1219_, 1, v___x_1214_);
                v___x_1220_ = l_Lean_Name_reprPrec(v_facet_1207_, v___x_1211_);
                v___x_1221_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1221_, 0, v___x_1219_);
                leanh::lean_ctor_set(v___x_1221_, 1, v___x_1220_);
                leanh::lean_inc(v___y_1213_);
                v___x_1222_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1222_, 0, v___y_1213_);
                leanh::lean_ctor_set(v___x_1222_, 1, v___x_1221_);
                v___x_1223_ = 0;
                v___x_1224_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1224_, 0, v___x_1222_);
                leanh::lean_ctor_set_uint8(
                    v___x_1224_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_1231_: *mut leanh::LeanObject,
    mut v_prec_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1233_ = l_Lake_instReprBuildKey_repr(v_x_1231_, v_prec_1232_);
    leanh::lean_dec(v_prec_1232_);
    return v_res_1233_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey_decEq(
    mut v_x_1236_: *mut leanh::LeanObject,
    mut v_x_1237_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1236_) {
        0 => {
            if leanh::lean_obj_tag(v_x_1237_) == 0 {
                let mut v_module_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1240_: u8 = 0;
                v_module_1238_ = leanh::lean_ctor_get(v_x_1236_, 0);
                v_module_1239_ = leanh::lean_ctor_get(v_x_1237_, 0);
                v___x_1240_ = lean_name_eq(v_module_1238_, v_module_1239_);
                return v___x_1240_;
            } else {
                let mut v___x_1241_: u8 = 0;
                v___x_1241_ = 0;
                return v___x_1241_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_1237_) == 1 {
                let mut v_package_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1244_: u8 = 0;
                v_package_1242_ = leanh::lean_ctor_get(v_x_1236_, 0);
                v_package_1243_ = leanh::lean_ctor_get(v_x_1237_, 0);
                v___x_1244_ = lean_name_eq(v_package_1242_, v_package_1243_);
                return v___x_1244_;
            } else {
                let mut v___x_1245_: u8 = 0;
                v___x_1245_ = 0;
                return v___x_1245_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_1237_) == 2 {
                let mut v_package_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1250_: u8 = 0;
                v_package_1246_ = leanh::lean_ctor_get(v_x_1236_, 0);
                v_module_1247_ = leanh::lean_ctor_get(v_x_1236_, 1);
                v_package_1248_ = leanh::lean_ctor_get(v_x_1237_, 0);
                v_module_1249_ = leanh::lean_ctor_get(v_x_1237_, 1);
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
            if leanh::lean_obj_tag(v_x_1237_) == 3 {
                let mut v_package_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1257_: u8 = 0;
                v_package_1253_ = leanh::lean_ctor_get(v_x_1236_, 0);
                v_target_1254_ = leanh::lean_ctor_get(v_x_1236_, 1);
                v_package_1255_ = leanh::lean_ctor_get(v_x_1237_, 0);
                v_target_1256_ = leanh::lean_ctor_get(v_x_1237_, 1);
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
            if leanh::lean_obj_tag(v_x_1237_) == 4 {
                let mut v_target_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_inst_1264_: u8 = 0;
                v_target_1260_ = leanh::lean_ctor_get(v_x_1236_, 0);
                v_facet_1261_ = leanh::lean_ctor_get(v_x_1236_, 1);
                v_target_1262_ = leanh::lean_ctor_get(v_x_1237_, 0);
                v_facet_1263_ = leanh::lean_ctor_get(v_x_1237_, 1);
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
    mut v_x_1267_: *mut leanh::LeanObject,
    mut v_x_1268_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1269_: u8 = 0;
    let mut v_r_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1269_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_1267_, v_x_1268_);
    leanh::lean_dec_ref(v_x_1268_);
    leanh::lean_dec_ref(v_x_1267_);
    v_r_1270_ = leanh::lean_box((v_res_1269_) as usize);
    return v_r_1270_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey(
    mut v_x_1271_: *mut leanh::LeanObject,
    mut v_x_1272_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1273_: u8 = 0;
    v___x_1273_ = l_Lake_instDecidableEqBuildKey_decEq(v_x_1271_, v_x_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lake_instDecidableEqBuildKey___boxed(
    mut v_x_1274_: *mut leanh::LeanObject,
    mut v_x_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1276_: u8 = 0;
    let mut v_r_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1276_ = l_Lake_instDecidableEqBuildKey(v_x_1274_, v_x_1275_);
    leanh::lean_dec_ref(v_x_1275_);
    leanh::lean_dec_ref(v_x_1274_);
    v_r_1277_ = leanh::lean_box((v_res_1276_) as usize);
    return v_r_1277_;
}
pub unsafe fn _init_l_Lake_instHashableBuildKey_hash___closed__0() -> u64 {
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u64 = 0;
    v___x_1278_ = leanh::lean_unsigned_to_nat(1723);
    v___x_1279_ = lean_uint64_of_nat(v___x_1278_);
    return v___x_1279_;
}
pub unsafe fn _init_l_Lake_instHashableBuildKey_hash___closed__1() -> u64 {
    let mut v___x_1280_: u64 = 0;
    let mut v___x_1281_: u64 = 0;
    let mut v___x_1282_: u64 = 0;
    v___x_1280_ = leanh::lean_uint64_once(
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
    v___x_1283_ = leanh::lean_uint64_once(
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
        _init_l_Lake_instHashableBuildKey_hash___closed__0,
    );
    v___x_1284_ = 1u64;
    v___x_1285_ = lean_uint64_mix_hash(v___x_1284_, v___x_1283_);
    return v___x_1285_;
}
pub unsafe fn l_Lake_instHashableBuildKey_hash(
    mut v_x_1286_: *mut leanh::LeanObject,
) -> u64 {
    let mut v_module_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: u64 = 0;
    let mut v___x_1289_: u64 = 0;
    let mut v_hash_1290_: u64 = 0;
    let mut v___x_1291_: u64 = 0;
    let mut v_package_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u64 = 0;
    let mut v___x_1294_: u64 = 0;
    let mut v_hash_1295_: u64 = 0;
    let mut v___x_1296_: u64 = 0;
    let mut v_package_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: u64 = 0;
    let mut v___y_1301_: u64 = 0;
    let mut v___x_1302_: u64 = 0;
    let mut v___x_1303_: u64 = 0;
    let mut v___x_1304_: u64 = 0;
    let mut v_hash_1305_: u64 = 0;
    let mut v___x_1306_: u64 = 0;
    let mut v___x_1307_: u64 = 0;
    let mut v_hash_1308_: u64 = 0;
    let mut v_package_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: u64 = 0;
    let mut v___y_1313_: u64 = 0;
    let mut v___x_1314_: u64 = 0;
    let mut v___x_1315_: u64 = 0;
    let mut v___x_1316_: u64 = 0;
    let mut v_hash_1317_: u64 = 0;
    let mut v___x_1318_: u64 = 0;
    let mut v___x_1319_: u64 = 0;
    let mut v_hash_1320_: u64 = 0;
    let mut v_target_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
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
            0 => match leanh::lean_obj_tag(v_x_1286_) {
                0 => {
                    v_module_1287_ = leanh::lean_ctor_get(v_x_1286_, 0);
                    v___x_1288_ = 0u64;
                    if leanh::lean_obj_tag(v_module_1287_) == 0 {
                        v___x_1289_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__1_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__1,
                        );
                        return v___x_1289_;
                    } else {
                        v_hash_1290_ = leanh::lean_ctor_get_uint64(
                            v_module_1287_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1291_ = lean_uint64_mix_hash(v___x_1288_, v_hash_1290_);
                        return v___x_1291_;
                    }
                }
                1 => {
                    v_package_1292_ = leanh::lean_ctor_get(v_x_1286_, 0);
                    v___x_1293_ = 1u64;
                    if leanh::lean_obj_tag(v_package_1292_) == 0 {
                        v___x_1294_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__2_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__2,
                        );
                        return v___x_1294_;
                    } else {
                        v_hash_1295_ = leanh::lean_ctor_get_uint64(
                            v_package_1292_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1296_ = lean_uint64_mix_hash(v___x_1293_, v_hash_1295_);
                        return v___x_1296_;
                    }
                }
                2 => {
                    v_package_1297_ = leanh::lean_ctor_get(v_x_1286_, 0);
                    v_module_1298_ = leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1299_ = 2u64;
                    if leanh::lean_obj_tag(v_package_1297_) == 0 {
                        v___x_1307_ = leanh::lean_uint64_once(
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
                        v_hash_1308_ = leanh::lean_ctor_get_uint64(
                            v_package_1297_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1301_ = v_hash_1308_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_package_1309_ = leanh::lean_ctor_get(v_x_1286_, 0);
                    v_target_1310_ = leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1311_ = 3u64;
                    if leanh::lean_obj_tag(v_package_1309_) == 0 {
                        v___x_1319_ = leanh::lean_uint64_once(
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
                        v_hash_1320_ = leanh::lean_ctor_get_uint64(
                            v_package_1309_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_1313_ = v_hash_1320_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v_target_1321_ = leanh::lean_ctor_get(v_x_1286_, 0);
                    v_facet_1322_ = leanh::lean_ctor_get(v_x_1286_, 1);
                    v___x_1323_ = 4u64;
                    v___x_1324_ = l_Lake_instHashableBuildKey_hash(v_target_1321_);
                    v___x_1325_ = lean_uint64_mix_hash(v___x_1323_, v___x_1324_);
                    if leanh::lean_obj_tag(v_facet_1322_) == 0 {
                        v___x_1326_ = leanh::lean_uint64_once(
                            core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lake_instHashableBuildKey_hash___closed__0_once
                            ),
                            _init_l_Lake_instHashableBuildKey_hash___closed__0,
                        );
                        v___x_1327_ = lean_uint64_mix_hash(v___x_1325_, v___x_1326_);
                        return v___x_1327_;
                    } else {
                        v_hash_1328_ = leanh::lean_ctor_get_uint64(
                            v_facet_1322_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___x_1329_ = lean_uint64_mix_hash(v___x_1325_, v_hash_1328_);
                        return v___x_1329_;
                    }
                }
            },
            1 => {
                v___x_1302_ = lean_uint64_mix_hash(v___x_1299_, v___y_1301_);
                if leanh::lean_obj_tag(v_module_1298_) == 0 {
                    v___x_1303_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
                        _init_l_Lake_instHashableBuildKey_hash___closed__0,
                    );
                    v___x_1304_ = lean_uint64_mix_hash(v___x_1302_, v___x_1303_);
                    return v___x_1304_;
                } else {
                    v_hash_1305_ = leanh::lean_ctor_get_uint64(
                        v_module_1298_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___x_1306_ = lean_uint64_mix_hash(v___x_1302_, v_hash_1305_);
                    return v___x_1306_;
                }
            }
            2 => {
                v___x_1314_ = lean_uint64_mix_hash(v___x_1311_, v___y_1313_);
                if leanh::lean_obj_tag(v_target_1310_) == 0 {
                    v___x_1315_ = leanh::lean_uint64_once(
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0),
                        core::ptr::addr_of_mut!(l_Lake_instHashableBuildKey_hash___closed__0_once),
                        _init_l_Lake_instHashableBuildKey_hash___closed__0,
                    );
                    v___x_1316_ = lean_uint64_mix_hash(v___x_1314_, v___x_1315_);
                    return v___x_1316_;
                } else {
                    v_hash_1317_ = leanh::lean_ctor_get_uint64(
                        v_target_1310_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
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
    mut v_x_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1331_: u64 = 0;
    let mut v_r_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1331_ = l_Lake_instHashableBuildKey_hash(v_x_1330_);
    leanh::lean_dec_ref(v_x_1330_);
    v_r_1332_ = leanh::lean_box_uint64(v_res_1331_);
    return v_r_1332_;
}
pub unsafe fn l_Lake_PartialBuildKey_mk(
    mut v_key_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_key_1335_);
    return v_key_1335_;
}
pub unsafe fn l_Lake_PartialBuildKey_mk___boxed(
    mut v_key_1336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1337_ = l_Lake_PartialBuildKey_mk(v_key_1336_);
    leanh::lean_dec_ref(v_key_1336_);
    return v_res_1337_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(
    mut v_x_1340_: *mut leanh::LeanObject,
    mut v_prec_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = l_Lake_instReprBuildKey_repr(v_x_1340_, v_prec_1341_);
    return v___x_1342_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1___boxed(
    mut v_x_1343_: *mut leanh::LeanObject,
    mut v_prec_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_instRepr___aux__1(
        v_x_1343_,
        v_prec_1344_,
    );
    leanh::lean_dec(v_prec_1344_);
    return v_res_1345_;
}
pub unsafe fn _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1353_ =
        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
    v___x_1354_ = lean_string_utf8_byte_size(v___x_1353_);
    return v___x_1354_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
    mut v_pkg_1358_: *mut leanh::LeanObject,
    mut v_target_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1364_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: u8 = 0;
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1360_ = leanh::lean_ctor_get(v_target_1359_, 0);
                v_startInclusive_1361_ = leanh::lean_ctor_get(v_target_1359_, 1);
                v_endExclusive_1362_ = leanh::lean_ctor_get(v_target_1359_, 2);
                v___x_1377_ = lean_nat_sub(v_endExclusive_1362_, v_startInclusive_1361_);
                v___x_1378_ = leanh::lean_unsigned_to_nat(0);
                v___x_1379_ = lean_nat_dec_eq(v___x_1377_, v___x_1378_);
                if v___x_1379_ == 0 {
                    v___x_1380_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
                    v___x_1382_ = lean_nat_dec_le(v___x_1381_, v___x_1377_);
                    leanh::lean_dec(v___x_1377_);
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
                    leanh::lean_dec(v___x_1377_);
                    leanh::lean_dec(v_pkg_1358_);
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
                    v___x_1367_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1367_, 0, v_pkg_1358_);
                    leanh::lean_ctor_set(v___x_1367_, 1, v_target_1366_);
                    v___x_1368_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1368_, 0, v___x_1367_);
                    return v___x_1368_;
                } else {
                    v___x_1369_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1370_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1371_ =
                        l_String_Slice_Pos_nextn(v_target_1359_, v___x_1370_, v___x_1369_);
                    v___x_1372_ = lean_nat_add(v_startInclusive_1361_, v___x_1371_);
                    leanh::lean_dec(v___x_1371_);
                    v___x_1373_ =
                        lean_string_utf8_extract(v_str_1360_, v___x_1372_, v_endExclusive_1362_);
                    leanh::lean_dec(v___x_1372_);
                    v_target_1374_ = l_Lake_stringToLegalOrSimpleName(v___x_1373_);
                    v___x_1375_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1375_, 0, v_pkg_1358_);
                    leanh::lean_ctor_set(v___x_1375_, 1, v_target_1374_);
                    v___x_1376_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1376_, 0, v___x_1375_);
                    return v___x_1376_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___boxed(
    mut v_pkg_1385_: *mut leanh::LeanObject,
    mut v_target_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
        v_pkg_1385_,
        v_target_1386_,
    );
    leanh::lean_dec_ref(v_target_1386_);
    return v_res_1387_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(
    mut v_s_1390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1391_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0;
    return v___x_1391_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___boxed(
    mut v_s_1392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1393_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v_s_1392_);
    leanh::lean_dec_ref(v_s_1392_);
    return v_res_1393_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(
    mut v_s_1394_: *mut leanh::LeanObject,
    mut v___x_1395_: *mut leanh::LeanObject,
    mut v___x_1396_: *mut leanh::LeanObject,
    mut v_a_1397_: *mut leanh::LeanObject,
    mut v_b_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v_startInclusive_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v___x_1415_: u32 = 0;
    let mut v___x_1416_: u32 = 0;
    let mut v___x_1417_: u8 = 0;
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1397_) == 0 {
                    v_currPos_1406_ = leanh::lean_ctor_get(v_a_1397_, 0);
                    v_searcher_1407_ = leanh::lean_ctor_get(v_a_1397_, 1);
                    v_isSharedCheck_1433_ = (!leanh::lean_is_exclusive(v_a_1397_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1409_ = v_a_1397_;
                        v_isShared_1410_ = v_isSharedCheck_1433_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1407_);
                        leanh::lean_inc(v_currPos_1406_);
                        leanh::lean_dec(v_a_1397_);
                        v___x_1409_ = leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1433_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1396_);
                    leanh::lean_dec_ref(v_s_1394_);
                    return v_b_1398_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_s_1394_);
                v___x_1403_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1403_, 0, v_s_1394_);
                leanh::lean_ctor_set(v___x_1403_, 1, v_startInclusive_1401_);
                leanh::lean_ctor_set(v___x_1403_, 2, v_endExclusive_1402_);
                v___x_1404_ = lean_array_push(v_b_1398_, v___x_1403_);
                v_a_1397_ = v_it_1400_;
                v_b_1398_ = v___x_1404_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1411_ = leanh::lean_ctor_get(v___x_1395_, 1);
                v_endExclusive_1412_ = leanh::lean_ctor_get(v___x_1395_, 2);
                v___x_1413_ = lean_nat_sub(v_endExclusive_1412_, v_startInclusive_1411_);
                v___x_1414_ = lean_nat_dec_eq(v_searcher_1407_, v___x_1413_);
                leanh::lean_dec(v___x_1413_);
                if v___x_1414_ == 0 {
                    v___x_1415_ = 47;
                    v___x_1416_ = lean_string_utf8_get_fast(v_s_1394_, v_searcher_1407_);
                    v___x_1417_ = lean_uint32_dec_eq(v___x_1416_, v___x_1415_);
                    if v___x_1417_ == 0 {
                        v___x_1418_ = lean_string_utf8_next_fast(v_s_1394_, v_searcher_1407_);
                        leanh::lean_dec(v_searcher_1407_);
                        if v_isShared_1410_ == 0 {
                            leanh::lean_ctor_set(v___x_1409_, 1, v___x_1418_);
                            v___x_1420_ = v___x_1409_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1422_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_currPos_1406_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1422_, 1, v___x_1418_);
                            v___x_1420_ = v_reuseFailAlloc_1422_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1423_ = lean_string_utf8_next_fast(v_s_1394_, v_searcher_1407_);
                        v___x_1424_ = lean_nat_sub(v___x_1423_, v_searcher_1407_);
                        v___x_1425_ = lean_nat_add(v_searcher_1407_, v___x_1424_);
                        leanh::lean_dec(v___x_1424_);
                        v_slice_1426_ = l_String_Slice_subslice_x21(
                            v___x_1395_,
                            v_currPos_1406_,
                            v_searcher_1407_,
                        );
                        leanh::lean_inc(v___x_1425_);
                        if v_isShared_1410_ == 0 {
                            leanh::lean_ctor_set(v___x_1409_, 1, v___x_1425_);
                            leanh::lean_ctor_set(v___x_1409_, 0, v___x_1425_);
                            v_nextIt_1428_ = v___x_1409_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1431_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1425_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1431_, 1, v___x_1425_);
                            v_nextIt_1428_ = v_reuseFailAlloc_1431_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1409_);
                    leanh::lean_dec(v_searcher_1407_);
                    v___x_1432_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_1396_);
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
                v_startInclusive_1429_ = leanh::lean_ctor_get(v_slice_1426_, 0);
                leanh::lean_inc(v_startInclusive_1429_);
                v_endExclusive_1430_ = leanh::lean_ctor_get(v_slice_1426_, 1);
                leanh::lean_inc(v_endExclusive_1430_);
                leanh::lean_dec_ref(v_slice_1426_);
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
    mut v_s_1434_: *mut leanh::LeanObject,
    mut v___x_1435_: *mut leanh::LeanObject,
    mut v___x_1436_: *mut leanh::LeanObject,
    mut v_a_1437_: *mut leanh::LeanObject,
    mut v_b_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1434_, v___x_1435_, v___x_1436_, v_a_1437_, v_b_1438_);
    leanh::lean_dec_ref(v___x_1435_);
    return v_res_1439_;
}
pub unsafe fn _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1451_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
    v___x_1452_ = lean_string_utf8_byte_size(v___x_1451_);
    return v___x_1452_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(
    mut v_s_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1472_: u8 = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: u8 = 0;
    let mut v___x_1477_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: u8 = 0;
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: u8 = 0;
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = leanh::lean_unsigned_to_nat(0);
                v___x_1457_ = lean_string_utf8_byte_size(v_s_1453_);
                leanh::lean_inc_ref(v_s_1453_);
                v___x_1458_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1458_, 0, v_s_1453_);
                leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
                leanh::lean_ctor_set(v___x_1458_, 2, v___x_1457_);
                v___x_1459_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0(v___x_1458_);
                v___x_1460_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__2;
                v___x_1461_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1453_, v___x_1458_, v___x_1457_, v___x_1459_, v___x_1460_);
                leanh::lean_dec_ref_known(v___x_1458_, 3);
                v___x_1462_ = lean_array_to_list(v___x_1461_);
                if leanh::lean_obj_tag(v___x_1462_) == 1 {
                    v_head_1463_ = leanh::lean_ctor_get(v___x_1462_, 0);
                    leanh::lean_inc(v_head_1463_);
                    v_tail_1464_ = leanh::lean_ctor_get(v___x_1462_, 1);
                    leanh::lean_inc(v_tail_1464_);
                    leanh::lean_dec_ref_known(v___x_1462_, 2);
                    if leanh::lean_obj_tag(v_tail_1464_) == 0 {
                        v_str_1468_ = leanh::lean_ctor_get(v_head_1463_, 0);
                        v_startInclusive_1469_ = leanh::lean_ctor_get(v_head_1463_, 1);
                        v_endExclusive_1470_ = leanh::lean_ctor_get(v_head_1463_, 2);
                        v___x_1498_ = lean_nat_sub(v_endExclusive_1470_, v_startInclusive_1469_);
                        v___x_1499_ = lean_nat_dec_eq(v___x_1498_, v___x_1456_);
                        if v___x_1499_ == 0 {
                            v___x_1500_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
                            v___x_1501_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
                            v___x_1502_ = lean_nat_dec_le(v___x_1501_, v___x_1498_);
                            leanh::lean_dec(v___x_1498_);
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
                            leanh::lean_dec(v___x_1498_);
                            leanh::lean_dec(v_head_1463_);
                            v___x_1504_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5;
                            return v___x_1504_;
                        }
                    } else {
                        v_head_1505_ = leanh::lean_ctor_get(v_tail_1464_, 0);
                        leanh::lean_inc(v_head_1505_);
                        v_tail_1506_ = leanh::lean_ctor_get(v_tail_1464_, 1);
                        leanh::lean_inc(v_tail_1506_);
                        leanh::lean_dec_ref_known(v_tail_1464_, 2);
                        if leanh::lean_obj_tag(v_tail_1506_) == 0 {
                            v_str_1518_ = leanh::lean_ctor_get(v_head_1463_, 0);
                            leanh::lean_inc_ref(v_str_1518_);
                            v_startInclusive_1519_ = leanh::lean_ctor_get(v_head_1463_, 1);
                            leanh::lean_inc(v_startInclusive_1519_);
                            v_endExclusive_1520_ = leanh::lean_ctor_get(v_head_1463_, 2);
                            leanh::lean_inc(v_endExclusive_1520_);
                            v___x_1521_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
                            v___x_1522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__7);
                            v___x_1523_ =
                                lean_nat_sub(v_endExclusive_1520_, v_startInclusive_1519_);
                            v___x_1524_ = lean_nat_dec_le(v___x_1522_, v___x_1523_);
                            leanh::lean_dec(v___x_1523_);
                            if v___x_1524_ == 0 {
                                leanh::lean_dec(v_head_1463_);
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
                                    leanh::lean_dec(v_head_1463_);
                                    v_str_1508_ = v_str_1518_;
                                    v_startInclusive_1509_ = v_startInclusive_1519_;
                                    v_endExclusive_1510_ = v_endExclusive_1520_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_1526_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1527_ = l_String_Slice_Pos_nextn(
                                        v_head_1463_,
                                        v___x_1456_,
                                        v___x_1526_,
                                    );
                                    leanh::lean_dec(v_head_1463_);
                                    v___x_1528_ = lean_nat_add(v_startInclusive_1519_, v___x_1527_);
                                    leanh::lean_dec(v___x_1527_);
                                    leanh::lean_dec(v_startInclusive_1519_);
                                    v_str_1508_ = v_str_1518_;
                                    v_startInclusive_1509_ = v___x_1528_;
                                    v_endExclusive_1510_ = v_endExclusive_1520_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_tail_1506_);
                            leanh::lean_dec(v_head_1505_);
                            leanh::lean_dec(v_head_1463_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1462_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1455_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__1;
                return v___x_1455_;
            }
            2 => {
                v___x_1466_ = leanh::lean_box(0);
                v___x_1467_ =
                    l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                        v___x_1466_,
                        v_head_1463_,
                    );
                leanh::lean_dec(v_head_1463_);
                return v___x_1467_;
            }
            3 => {
                if v___y_1472_ == 0 {
                    v___x_1473_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1474_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1), core::ptr::addr_of_mut!(l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1_once), _init_l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__1);
                    v___x_1475_ = lean_nat_sub(v_endExclusive_1470_, v_startInclusive_1469_);
                    v___x_1476_ = lean_nat_dec_le(v___x_1474_, v___x_1475_);
                    leanh::lean_dec(v___x_1475_);
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
                            leanh::lean_inc(v_endExclusive_1470_);
                            leanh::lean_inc(v_startInclusive_1469_);
                            leanh::lean_inc_ref(v_str_1468_);
                            v___x_1478_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1479_ =
                                l_String_Slice_Pos_nextn(v_head_1463_, v___x_1456_, v___x_1478_);
                            leanh::lean_dec(v_head_1463_);
                            v___x_1480_ = lean_nat_add(v_startInclusive_1469_, v___x_1479_);
                            leanh::lean_dec(v___x_1479_);
                            leanh::lean_dec(v_startInclusive_1469_);
                            v___x_1481_ = lean_nat_sub(v_endExclusive_1470_, v___x_1480_);
                            v___x_1482_ = lean_nat_dec_eq(v___x_1481_, v___x_1456_);
                            leanh::lean_dec(v___x_1481_);
                            if v___x_1482_ == 0 {
                                v___x_1483_ = lean_string_utf8_extract(
                                    v_str_1468_,
                                    v___x_1480_,
                                    v_endExclusive_1470_,
                                );
                                leanh::lean_dec(v_endExclusive_1470_);
                                leanh::lean_dec(v___x_1480_);
                                leanh::lean_dec_ref(v_str_1468_);
                                v___x_1484_ = l_Lake_stringToLegalOrSimpleName(v___x_1483_);
                                v___x_1485_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1485_, 0, v___x_1484_);
                                v___x_1486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1486_, 0, v___x_1485_);
                                return v___x_1486_;
                            } else {
                                leanh::lean_dec(v___x_1480_);
                                leanh::lean_dec(v_endExclusive_1470_);
                                leanh::lean_dec_ref(v_str_1468_);
                                v___x_1487_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__4;
                                return v___x_1487_;
                            }
                        }
                    }
                } else {
                    leanh::lean_inc(v_endExclusive_1470_);
                    leanh::lean_inc(v_startInclusive_1469_);
                    leanh::lean_inc_ref(v_str_1468_);
                    v___x_1488_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1489_ = l_String_Slice_Pos_nextn(v_head_1463_, v___x_1456_, v___x_1488_);
                    leanh::lean_dec(v_head_1463_);
                    v___x_1490_ = lean_nat_add(v_startInclusive_1469_, v___x_1489_);
                    leanh::lean_dec(v___x_1489_);
                    leanh::lean_dec(v_startInclusive_1469_);
                    v___x_1491_ = lean_nat_sub(v_endExclusive_1470_, v___x_1490_);
                    v___x_1492_ = lean_nat_dec_eq(v___x_1491_, v___x_1456_);
                    leanh::lean_dec(v___x_1491_);
                    if v___x_1492_ == 0 {
                        v___x_1493_ = lean_string_utf8_extract(
                            v_str_1468_,
                            v___x_1490_,
                            v_endExclusive_1470_,
                        );
                        leanh::lean_dec(v_endExclusive_1470_);
                        leanh::lean_dec(v___x_1490_);
                        leanh::lean_dec_ref(v_str_1468_);
                        v___x_1494_ = l_Lake_stringToLegalOrSimpleName(v___x_1493_);
                        v___x_1495_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1495_, 0, v___x_1494_);
                        v___x_1496_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1496_, 0, v___x_1495_);
                        return v___x_1496_;
                    } else {
                        leanh::lean_dec(v___x_1490_);
                        leanh::lean_dec(v_endExclusive_1470_);
                        leanh::lean_dec_ref(v_str_1468_);
                        v___x_1497_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__5;
                        return v___x_1497_;
                    }
                }
            }
            4 => {
                v___x_1511_ = lean_nat_sub(v_endExclusive_1510_, v_startInclusive_1509_);
                v___x_1512_ = lean_nat_dec_eq(v___x_1511_, v___x_1456_);
                leanh::lean_dec(v___x_1511_);
                if v___x_1512_ == 0 {
                    v___x_1513_ = lean_string_utf8_extract(
                        v_str_1508_,
                        v_startInclusive_1509_,
                        v_endExclusive_1510_,
                    );
                    leanh::lean_dec(v_endExclusive_1510_);
                    leanh::lean_dec(v_startInclusive_1509_);
                    leanh::lean_dec_ref(v_str_1508_);
                    v___x_1514_ = l_Lake_stringToLegalOrSimpleName(v___x_1513_);
                    v___x_1515_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                            v___x_1514_,
                            v_head_1505_,
                        );
                    leanh::lean_dec(v_head_1505_);
                    return v___x_1515_;
                } else {
                    leanh::lean_dec(v_endExclusive_1510_);
                    leanh::lean_dec(v_startInclusive_1509_);
                    leanh::lean_dec_ref(v_str_1508_);
                    v___x_1516_ = leanh::lean_box(0);
                    v___x_1517_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget(
                            v___x_1516_,
                            v_head_1505_,
                        );
                    leanh::lean_dec(v_head_1505_);
                    return v___x_1517_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(
    mut v_s_1529_: *mut leanh::LeanObject,
    mut v___x_1530_: *mut leanh::LeanObject,
    mut v___x_1531_: *mut leanh::LeanObject,
    mut v_inst_1532_: *mut leanh::LeanObject,
    mut v_R_1533_: *mut leanh::LeanObject,
    mut v_a_1534_: *mut leanh::LeanObject,
    mut v_b_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___redArg(v_s_1529_, v___x_1530_, v___x_1531_, v_a_1534_, v_b_1535_);
    return v___x_1536_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1___boxed(
    mut v_s_1537_: *mut leanh::LeanObject,
    mut v___x_1538_: *mut leanh::LeanObject,
    mut v___x_1539_: *mut leanh::LeanObject,
    mut v_inst_1540_: *mut leanh::LeanObject,
    mut v_R_1541_: *mut leanh::LeanObject,
    mut v_a_1542_: *mut leanh::LeanObject,
    mut v_b_1543_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1544_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__1(v_s_1537_, v___x_1538_, v___x_1539_, v_inst_1540_, v_R_1541_, v_a_1542_, v_b_1543_);
    leanh::lean_dec_ref(v___x_1538_);
    return v_res_1544_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(
    mut v_s_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_String_Slice_splitToSubslice___at___00__private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget_spec__0___closed__0;
    return v___x_1546_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0___boxed(
    mut v_s_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1548_ =
        l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v_s_1547_);
    leanh::lean_dec_ref(v_s_1547_);
    return v_res_1548_;
}
pub unsafe fn l_panic___at___00Lake_PartialBuildKey_parse_spec__2(
    mut v_msg_1550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2___closed__0;
    v___x_1552_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1552_, 0, v___x_1551_);
    v___x_1553_ = lean_panic_fn_borrowed(v___x_1552_, v_msg_1550_);
    leanh::lean_dec_ref_known(v___x_1552_, 1);
    return v___x_1553_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(
    mut v_s_1554_: *mut leanh::LeanObject,
    mut v___x_1555_: *mut leanh::LeanObject,
    mut v___x_1556_: *mut leanh::LeanObject,
    mut v_a_1557_: *mut leanh::LeanObject,
    mut v_b_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v_startInclusive_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: u32 = 0;
    let mut v___x_1577_: u32 = 0;
    let mut v___x_1578_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1557_) == 0 {
                    v_currPos_1567_ = leanh::lean_ctor_get(v_a_1557_, 0);
                    v_searcher_1568_ = leanh::lean_ctor_get(v_a_1557_, 1);
                    v_isSharedCheck_1594_ = (!leanh::lean_is_exclusive(v_a_1557_)) as u8;
                    if v_isSharedCheck_1594_ == 0 {
                        v___x_1570_ = v_a_1557_;
                        v_isShared_1571_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1568_);
                        leanh::lean_inc(v_currPos_1567_);
                        leanh::lean_dec(v_a_1557_);
                        v___x_1570_ = leanh::lean_box(0);
                        v_isShared_1571_ = v_isSharedCheck_1594_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1556_);
                    leanh::lean_dec_ref(v_s_1554_);
                    return v_b_1558_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_s_1554_);
                v___x_1563_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1563_, 0, v_s_1554_);
                leanh::lean_ctor_set(v___x_1563_, 1, v_startInclusive_1561_);
                leanh::lean_ctor_set(v___x_1563_, 2, v_endExclusive_1562_);
                v___x_1564_ = l_String_Slice_toString(v___x_1563_);
                leanh::lean_dec_ref_known(v___x_1563_, 3);
                v___x_1565_ = lean_array_push(v_b_1558_, v___x_1564_);
                v_a_1557_ = v_it_1560_;
                v_b_1558_ = v___x_1565_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1572_ = leanh::lean_ctor_get(v___x_1555_, 1);
                v_endExclusive_1573_ = leanh::lean_ctor_get(v___x_1555_, 2);
                v___x_1574_ = lean_nat_sub(v_endExclusive_1573_, v_startInclusive_1572_);
                v___x_1575_ = lean_nat_dec_eq(v_searcher_1568_, v___x_1574_);
                leanh::lean_dec(v___x_1574_);
                if v___x_1575_ == 0 {
                    v___x_1576_ = 58;
                    v___x_1577_ = lean_string_utf8_get_fast(v_s_1554_, v_searcher_1568_);
                    v___x_1578_ = lean_uint32_dec_eq(v___x_1577_, v___x_1576_);
                    if v___x_1578_ == 0 {
                        v___x_1579_ = lean_string_utf8_next_fast(v_s_1554_, v_searcher_1568_);
                        leanh::lean_dec(v_searcher_1568_);
                        if v_isShared_1571_ == 0 {
                            leanh::lean_ctor_set(v___x_1570_, 1, v___x_1579_);
                            v___x_1581_ = v___x_1570_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1583_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_currPos_1567_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1583_, 1, v___x_1579_);
                            v___x_1581_ = v_reuseFailAlloc_1583_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1584_ = lean_string_utf8_next_fast(v_s_1554_, v_searcher_1568_);
                        v___x_1585_ = lean_nat_sub(v___x_1584_, v_searcher_1568_);
                        v___x_1586_ = lean_nat_add(v_searcher_1568_, v___x_1585_);
                        leanh::lean_dec(v___x_1585_);
                        v_slice_1587_ = l_String_Slice_subslice_x21(
                            v___x_1555_,
                            v_currPos_1567_,
                            v_searcher_1568_,
                        );
                        leanh::lean_inc(v___x_1586_);
                        if v_isShared_1571_ == 0 {
                            leanh::lean_ctor_set(v___x_1570_, 1, v___x_1586_);
                            leanh::lean_ctor_set(v___x_1570_, 0, v___x_1586_);
                            v_nextIt_1589_ = v___x_1570_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1592_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1586_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1592_, 1, v___x_1586_);
                            v_nextIt_1589_ = v_reuseFailAlloc_1592_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1570_);
                    leanh::lean_dec(v_searcher_1568_);
                    v___x_1593_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_1556_);
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
                v_startInclusive_1590_ = leanh::lean_ctor_get(v_slice_1587_, 0);
                leanh::lean_inc(v_startInclusive_1590_);
                v_endExclusive_1591_ = leanh::lean_ctor_get(v_slice_1587_, 1);
                leanh::lean_inc(v_endExclusive_1591_);
                leanh::lean_dec_ref(v_slice_1587_);
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
    mut v_s_1595_: *mut leanh::LeanObject,
    mut v___x_1596_: *mut leanh::LeanObject,
    mut v___x_1597_: *mut leanh::LeanObject,
    mut v_a_1598_: *mut leanh::LeanObject,
    mut v_b_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1595_, v___x_1596_, v___x_1597_, v_a_1598_, v_b_1599_);
    leanh::lean_dec_ref(v___x_1596_);
    return v_res_1600_;
}
pub unsafe fn l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(
    mut v_x_1604_: *mut leanh::LeanObject,
    mut v_x_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: u8 = 0;
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1621_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1605_) == 0 {
                    v___x_1606_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1606_, 0, v_x_1604_);
                    return v___x_1606_;
                } else {
                    v_head_1607_ = leanh::lean_ctor_get(v_x_1605_, 0);
                    v_tail_1608_ = leanh::lean_ctor_get(v_x_1605_, 1);
                    v_isSharedCheck_1621_ = (!leanh::lean_is_exclusive(v_x_1605_)) as u8;
                    if v_isSharedCheck_1621_ == 0 {
                        v___x_1610_ = v_x_1605_;
                        v_isShared_1611_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1608_);
                        leanh::lean_inc(v_head_1607_);
                        leanh::lean_dec(v_x_1605_);
                        v___x_1610_ = leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1621_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1612_ = lean_string_utf8_byte_size(v_head_1607_);
                v___x_1613_ = leanh::lean_unsigned_to_nat(0);
                v___x_1614_ = lean_nat_dec_eq(v___x_1612_, v___x_1613_);
                if v___x_1614_ == 0 {
                    v___x_1615_ = l_Lake_stringToLegalOrSimpleName(v_head_1607_);
                    if v_isShared_1611_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1610_, 4);
                        leanh::lean_ctor_set(v___x_1610_, 1, v___x_1615_);
                        leanh::lean_ctor_set(v___x_1610_, 0, v_x_1604_);
                        v___x_1617_ = v___x_1610_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1619_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_x_1604_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1619_, 1, v___x_1615_);
                        v___x_1617_ = v_reuseFailAlloc_1619_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1610_);
                    leanh::lean_dec(v_tail_1608_);
                    leanh::lean_dec(v_head_1607_);
                    leanh::lean_dec_ref(v_x_1604_);
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
pub unsafe fn _init_l_Lake_PartialBuildKey_parse___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1627_ = l_Lake_PartialBuildKey_parse___closed__3;
    v___x_1628_ = leanh::lean_unsigned_to_nat(4);
    v___x_1629_ = leanh::lean_unsigned_to_nat(65);
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
    mut v_s_1636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: u8 = 0;
    v___x_1637_ = lean_string_utf8_byte_size(v_s_1636_);
    v___x_1638_ = leanh::lean_unsigned_to_nat(0);
    v___x_1639_ = lean_nat_dec_eq(v___x_1637_, v___x_1638_);
    if v___x_1639_ == 0 {
        let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_s_1636_);
        v___x_1640_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_1640_, 0, v_s_1636_);
        leanh::lean_ctor_set(v___x_1640_, 1, v___x_1638_);
        leanh::lean_ctor_set(v___x_1640_, 2, v___x_1637_);
        v___x_1641_ =
            l_String_Slice_splitToSubslice___at___00Lake_PartialBuildKey_parse_spec__0(v___x_1640_);
        v___x_1642_ = l_Lake_PartialBuildKey_parse___closed__0;
        v___x_1643_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1636_, v___x_1640_, v___x_1637_, v___x_1641_, v___x_1642_);
        leanh::lean_dec_ref_known(v___x_1640_, 3);
        v___x_1644_ = lean_array_to_list(v___x_1643_);
        if leanh::lean_obj_tag(v___x_1644_) == 0 {
            let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1645_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lake_PartialBuildKey_parse___closed__4),
                core::ptr::addr_of_mut!(l_Lake_PartialBuildKey_parse___closed__4_once),
                _init_l_Lake_PartialBuildKey_parse___closed__4,
            );
            v___x_1646_ = l_panic___at___00Lake_PartialBuildKey_parse_spec__2(v___x_1645_);
            return v___x_1646_;
        } else {
            let mut v_head_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1647_ = leanh::lean_ctor_get(v___x_1644_, 0);
            leanh::lean_inc(v_head_1647_);
            v_tail_1648_ = leanh::lean_ctor_get(v___x_1644_, 1);
            leanh::lean_inc(v_tail_1648_);
            leanh::lean_dec_ref_known(v___x_1644_, 2);
            v___x_1649_ =
                l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget(v_head_1647_);
            if leanh::lean_obj_tag(v___x_1649_) == 0 {
                leanh::lean_dec(v_tail_1648_);
                return v___x_1649_;
            } else {
                let mut v_a_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_1650_ = leanh::lean_ctor_get(v___x_1649_, 0);
                leanh::lean_inc(v_a_1650_);
                leanh::lean_dec_ref_known(v___x_1649_, 1);
                v___x_1651_ = l_List_foldlM___at___00Lake_PartialBuildKey_parse_spec__3(
                    v_a_1650_,
                    v_tail_1648_,
                );
                return v___x_1651_;
            }
        }
    } else {
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1636_);
        v___x_1652_ = l_Lake_PartialBuildKey_parse___closed__6;
        return v___x_1652_;
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(
    mut v_s_1653_: *mut leanh::LeanObject,
    mut v___x_1654_: *mut leanh::LeanObject,
    mut v___x_1655_: *mut leanh::LeanObject,
    mut v_inst_1656_: *mut leanh::LeanObject,
    mut v_R_1657_: *mut leanh::LeanObject,
    mut v_a_1658_: *mut leanh::LeanObject,
    mut v_b_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1660_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___redArg(v_s_1653_, v___x_1654_, v___x_1655_, v_a_1658_, v_b_1659_);
    return v___x_1660_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1___boxed(
    mut v_s_1661_: *mut leanh::LeanObject,
    mut v___x_1662_: *mut leanh::LeanObject,
    mut v___x_1663_: *mut leanh::LeanObject,
    mut v_inst_1664_: *mut leanh::LeanObject,
    mut v_R_1665_: *mut leanh::LeanObject,
    mut v_a_1666_: *mut leanh::LeanObject,
    mut v_b_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_PartialBuildKey_parse_spec__1(v_s_1661_, v___x_1662_, v___x_1663_, v_inst_1664_, v_R_1665_, v_a_1666_, v_b_1667_);
    leanh::lean_dec_ref(v___x_1662_);
    return v_res_1668_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
    mut v_p_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_p_1669_) {
        0 => {
            return v_p_1669_;
        }
        2 => {
            let mut v_pre_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pre_1670_ = leanh::lean_ctor_get(v_p_1669_, 0);
            if leanh::lean_obj_tag(v_pre_1670_) == 0 {
                return v_pre_1670_;
            } else {
                leanh::lean_inc(v_pre_1670_);
                return v_pre_1670_;
            }
        }
        _ => {
            leanh::lean_inc(v_p_1669_);
            return v_p_1669_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName___boxed(
    mut v_p_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1672_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(v_p_1671_);
    leanh::lean_dec(v_p_1671_);
    return v_res_1672_;
}
pub unsafe fn l_Lake_PartialBuildKey_toString(
    mut v_x_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_module_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: u8 = 0;
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: u8 = 0;
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: u8 = 0;
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1676_) {
                0 => {
                    v_module_1677_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc(v_module_1677_);
                    leanh::lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1678_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                    v___x_1679_ = 1;
                    v___x_1680_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1677_,
                        v___x_1679_,
                    );
                    v___x_1681_ = lean_string_append(v___x_1678_, v___x_1680_);
                    leanh::lean_dec_ref(v___x_1680_);
                    return v___x_1681_;
                }
                1 => {
                    v_package_1682_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc(v_package_1682_);
                    leanh::lean_dec_ref_known(v_x_1676_, 1);
                    v___x_1683_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1682_,
                        );
                    leanh::lean_dec(v_package_1682_);
                    if leanh::lean_obj_tag(v___x_1683_) == 0 {
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
                        leanh::lean_dec_ref(v___x_1687_);
                        return v___x_1688_;
                    }
                }
                2 => {
                    v_package_1689_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc(v_package_1689_);
                    v_module_1690_ = leanh::lean_ctor_get(v_x_1676_, 1);
                    leanh::lean_inc(v_module_1690_);
                    leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1691_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1689_,
                        );
                    leanh::lean_dec(v_package_1689_);
                    if leanh::lean_obj_tag(v___x_1691_) == 0 {
                        v___x_1692_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
                        v___x_1693_ = 1;
                        v___x_1694_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_module_1690_,
                                v___x_1693_,
                            );
                        v___x_1695_ = lean_string_append(v___x_1692_, v___x_1694_);
                        leanh::lean_dec_ref(v___x_1694_);
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
                        leanh::lean_dec_ref(v___x_1700_);
                        return v___x_1701_;
                    }
                }
                3 => {
                    v_package_1702_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc(v_package_1702_);
                    v_target_1703_ = leanh::lean_ctor_get(v_x_1676_, 1);
                    leanh::lean_inc(v_target_1703_);
                    leanh::lean_dec_ref_known(v_x_1676_, 2);
                    v___x_1704_ =
                        l___private_Lake_Build_Key_0__Lake_PartialBuildKey_toString_getPkgName(
                            v_package_1702_,
                        );
                    leanh::lean_dec(v_package_1702_);
                    if leanh::lean_obj_tag(v___x_1704_) == 0 {
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
                        leanh::lean_dec_ref(v___x_1711_);
                        return v___x_1712_;
                    }
                }
                _ => {
                    v_target_1713_ = leanh::lean_ctor_get(v_x_1676_, 0);
                    leanh::lean_inc_ref(v_target_1713_);
                    v_facet_1714_ = leanh::lean_ctor_get(v_x_1676_, 1);
                    leanh::lean_inc(v_facet_1714_);
                    leanh::lean_dec_ref_known(v_x_1676_, 2);
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
                        leanh::lean_dec_ref(v___x_1720_);
                        return v___x_1721_;
                    } else {
                        leanh::lean_dec(v_facet_1714_);
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
    mut v_module_1725_: *mut leanh::LeanObject,
    mut v_facet_1726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1727_, 0, v_module_1725_);
    v___x_1728_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1728_, 0, v___x_1727_);
    leanh::lean_ctor_set(v___x_1728_, 1, v_facet_1726_);
    return v___x_1728_;
}
pub unsafe fn l_Lake_BuildKey_packageFacet(
    mut v_package_1729_: *mut leanh::LeanObject,
    mut v_facet_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1731_, 0, v_package_1729_);
    v___x_1732_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1732_, 0, v___x_1731_);
    leanh::lean_ctor_set(v___x_1732_, 1, v_facet_1730_);
    return v___x_1732_;
}
pub unsafe fn l_Lake_BuildKey_packageModuleFacet(
    mut v_package_1733_: *mut leanh::LeanObject,
    mut v_module_1734_: *mut leanh::LeanObject,
    mut v_facet_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1736_, 0, v_package_1733_);
    leanh::lean_ctor_set(v___x_1736_, 1, v_module_1734_);
    v___x_1737_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1737_, 0, v___x_1736_);
    leanh::lean_ctor_set(v___x_1737_, 1, v_facet_1735_);
    return v___x_1737_;
}
pub unsafe fn l_Lake_BuildKey_targetFacet(
    mut v_package_1738_: *mut leanh::LeanObject,
    mut v_target_1739_: *mut leanh::LeanObject,
    mut v_facet_1740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1741_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1741_, 0, v_package_1738_);
    leanh::lean_ctor_set(v___x_1741_, 1, v_target_1739_);
    v___x_1742_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1742_, 0, v___x_1741_);
    leanh::lean_ctor_set(v___x_1742_, 1, v_facet_1740_);
    return v___x_1742_;
}
pub unsafe fn l_Lake_BuildKey_customTarget(
    mut v_package_1743_: *mut leanh::LeanObject,
    mut v_target_1744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1745_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1745_, 0, v_package_1743_);
    leanh::lean_ctor_set(v___x_1745_, 1, v_target_1744_);
    return v___x_1745_;
}
pub unsafe fn l_Lake_BuildKey_toString(
    mut v_x_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1746_) {
        0 => {
            let mut v_module_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: u8 = 0;
            let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_module_1747_ = leanh::lean_ctor_get(v_x_1746_, 0);
            leanh::lean_inc(v_module_1747_);
            leanh::lean_dec_ref_known(v_x_1746_, 1);
            v___x_1748_ = l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parsePackageTarget___closed__0;
            v___x_1749_ = 1;
            v___x_1750_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_module_1747_,
                v___x_1749_,
            );
            v___x_1751_ = lean_string_append(v___x_1748_, v___x_1750_);
            leanh::lean_dec_ref(v___x_1750_);
            return v___x_1751_;
        }
        1 => {
            let mut v_package_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1755_: u8 = 0;
            let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_package_1752_ = leanh::lean_ctor_get(v_x_1746_, 0);
            leanh::lean_inc(v_package_1752_);
            leanh::lean_dec_ref_known(v_x_1746_, 1);
            v___x_1753_ =
                l___private_Lake_Build_Key_0__Lake_PartialBuildKey_parse_parseTarget___closed__6;
            v___x_1754_ = l_Lean_Name_getPrefix(v_package_1752_);
            leanh::lean_dec(v_package_1752_);
            v___x_1755_ = 1;
            v___x_1756_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v___x_1754_,
                v___x_1755_,
            );
            v___x_1757_ = lean_string_append(v___x_1753_, v___x_1756_);
            leanh::lean_dec_ref(v___x_1756_);
            return v___x_1757_;
        }
        2 => {
            let mut v_package_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: u8 = 0;
            let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_package_1758_ = leanh::lean_ctor_get(v_x_1746_, 0);
            leanh::lean_inc(v_package_1758_);
            v_module_1759_ = leanh::lean_ctor_get(v_x_1746_, 1);
            leanh::lean_inc(v_module_1759_);
            leanh::lean_dec_ref_known(v_x_1746_, 2);
            v___x_1760_ = l_Lean_Name_getPrefix(v_package_1758_);
            leanh::lean_dec(v_package_1758_);
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
            leanh::lean_dec_ref(v___x_1765_);
            return v___x_1766_;
        }
        3 => {
            let mut v_package_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1770_: u8 = 0;
            let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_package_1767_ = leanh::lean_ctor_get(v_x_1746_, 0);
            leanh::lean_inc(v_package_1767_);
            v_target_1768_ = leanh::lean_ctor_get(v_x_1746_, 1);
            leanh::lean_inc(v_target_1768_);
            leanh::lean_dec_ref_known(v_x_1746_, 2);
            v___x_1769_ = l_Lean_Name_getPrefix(v_package_1767_);
            leanh::lean_dec(v_package_1767_);
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
            leanh::lean_dec_ref(v___x_1774_);
            return v___x_1775_;
        }
        _ => {
            let mut v_target_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1782_: u8 = 0;
            let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_target_1776_ = leanh::lean_ctor_get(v_x_1746_, 0);
            leanh::lean_inc_ref(v_target_1776_);
            v_facet_1777_ = leanh::lean_ctor_get(v_x_1746_, 1);
            leanh::lean_inc(v_facet_1777_);
            leanh::lean_dec_ref_known(v_x_1746_, 2);
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
            leanh::lean_dec_ref(v___x_1783_);
            return v___x_1784_;
        }
    }
}
pub unsafe fn l_Lake_BuildKey_toSimpleString(
    mut v_x_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_p_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: u8 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_facet_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_package_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1785_) {
                0 => {
                    v_module_1796_ = leanh::lean_ctor_get(v_x_1785_, 0);
                    leanh::lean_inc(v_module_1796_);
                    leanh::lean_dec_ref_known(v_x_1785_, 1);
                    v___x_1797_ = 1;
                    v___x_1798_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_module_1796_,
                        v___x_1797_,
                    );
                    return v___x_1798_;
                }
                1 => {
                    v_package_1799_ = leanh::lean_ctor_get(v_x_1785_, 0);
                    leanh::lean_inc(v_package_1799_);
                    leanh::lean_dec_ref_known(v_x_1785_, 1);
                    v___x_1800_ = l_Lean_Name_getPrefix(v_package_1799_);
                    leanh::lean_dec(v_package_1799_);
                    v___x_1801_ = 1;
                    v___x_1802_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_1800_,
                        v___x_1801_,
                    );
                    return v___x_1802_;
                }
                4 => {
                    v_target_1803_ = leanh::lean_ctor_get(v_x_1785_, 0);
                    leanh::lean_inc_ref(v_target_1803_);
                    v_facet_1804_ = leanh::lean_ctor_get(v_x_1785_, 1);
                    leanh::lean_inc(v_facet_1804_);
                    leanh::lean_dec_ref_known(v_x_1785_, 2);
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
                    leanh::lean_dec_ref(v___x_1810_);
                    return v___x_1811_;
                }
                _ => {
                    v_package_1812_ = leanh::lean_ctor_get(v_x_1785_, 0);
                    leanh::lean_inc(v_package_1812_);
                    v_module_1813_ = leanh::lean_ctor_get(v_x_1785_, 1);
                    leanh::lean_inc(v_module_1813_);
                    leanh::lean_dec_ref(v_x_1785_);
                    v_p_1787_ = v_package_1812_;
                    v_m_1788_ = v_module_1813_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1789_ = l_Lean_Name_getPrefix(v_p_1787_);
                leanh::lean_dec(v_p_1787_);
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
                leanh::lean_dec_ref(v___x_1794_);
                return v___x_1795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_BuildKey_quickCmp(
    mut v_k_1816_: *mut leanh::LeanObject,
    mut v_k_x27_1817_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_k_1816_) {
        0 => {
            if leanh::lean_obj_tag(v_k_x27_1817_) == 0 {
                let mut v_module_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1820_: u8 = 0;
                v_module_1818_ = leanh::lean_ctor_get(v_k_1816_, 0);
                v_module_1819_ = leanh::lean_ctor_get(v_k_x27_1817_, 0);
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
        1 => match leanh::lean_obj_tag(v_k_x27_1817_) {
            0 => {
                let mut v___x_1822_: u8 = 0;
                v___x_1822_ = 2;
                return v___x_1822_;
            }
            1 => {
                let mut v_package_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1825_: u8 = 0;
                v_package_1823_ = leanh::lean_ctor_get(v_k_1816_, 0);
                v_package_1824_ = leanh::lean_ctor_get(v_k_x27_1817_, 0);
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
        2 => match leanh::lean_obj_tag(v_k_x27_1817_) {
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
                let mut v_package_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_module_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1833_: u8 = 0;
                v_package_1829_ = leanh::lean_ctor_get(v_k_1816_, 0);
                v_module_1830_ = leanh::lean_ctor_get(v_k_1816_, 1);
                v_package_1831_ = leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_module_1832_ = leanh::lean_ctor_get(v_k_x27_1817_, 1);
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
        3 => match leanh::lean_obj_tag(v_k_x27_1817_) {
            4 => {
                let mut v___x_1836_: u8 = 0;
                v___x_1836_ = 0;
                return v___x_1836_;
            }
            3 => {
                let mut v_package_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_package_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1841_: u8 = 0;
                v_package_1837_ = leanh::lean_ctor_get(v_k_1816_, 0);
                v_target_1838_ = leanh::lean_ctor_get(v_k_1816_, 1);
                v_package_1839_ = leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_target_1840_ = leanh::lean_ctor_get(v_k_x27_1817_, 1);
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
            if leanh::lean_obj_tag(v_k_x27_1817_) == 4 {
                let mut v_target_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_target_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_facet_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1848_: u8 = 0;
                v_target_1844_ = leanh::lean_ctor_get(v_k_1816_, 0);
                v_facet_1845_ = leanh::lean_ctor_get(v_k_1816_, 1);
                v_target_1846_ = leanh::lean_ctor_get(v_k_x27_1817_, 0);
                v_facet_1847_ = leanh::lean_ctor_get(v_k_x27_1817_, 1);
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
    mut v_k_1851_: *mut leanh::LeanObject,
    mut v_k_x27_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1853_: u8 = 0;
    let mut v_r_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1853_ = l_Lake_BuildKey_quickCmp(v_k_1851_, v_k_x27_1852_);
    leanh::lean_dec_ref(v_k_x27_1852_);
    leanh::lean_dec_ref(v_k_1851_);
    v_r_1854_ = leanh::lean_box((v_res_1853_) as usize);
    return v_r_1854_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter___redArg(
    mut v_x_1855_: *mut leanh::LeanObject,
    mut v_h__1_1856_: *mut leanh::LeanObject,
    mut v_h__2_1857_: *mut leanh::LeanObject,
    mut v_h__3_1858_: *mut leanh::LeanObject,
    mut v_h__4_1859_: *mut leanh::LeanObject,
    mut v_h__5_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1855_) {
        0 => {
            let mut v_module_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1860_);
            leanh::lean_dec(v_h__4_1859_);
            leanh::lean_dec(v_h__3_1858_);
            leanh::lean_dec(v_h__2_1857_);
            v_module_1861_ = leanh::lean_ctor_get(v_x_1855_, 0);
            leanh::lean_inc(v_module_1861_);
            leanh::lean_dec_ref_known(v_x_1855_, 1);
            v___x_1862_ = leanh::lean_apply_1(v_h__1_1856_, v_module_1861_);
            return v___x_1862_;
        }
        1 => {
            let mut v_package_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1860_);
            leanh::lean_dec(v_h__4_1859_);
            leanh::lean_dec(v_h__3_1858_);
            leanh::lean_dec(v_h__1_1856_);
            v_package_1863_ = leanh::lean_ctor_get(v_x_1855_, 0);
            leanh::lean_inc(v_package_1863_);
            leanh::lean_dec_ref_known(v_x_1855_, 1);
            v___x_1864_ = leanh::lean_apply_1(v_h__2_1857_, v_package_1863_);
            return v___x_1864_;
        }
        2 => {
            let mut v_package_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1860_);
            leanh::lean_dec(v_h__4_1859_);
            leanh::lean_dec(v_h__2_1857_);
            leanh::lean_dec(v_h__1_1856_);
            v_package_1865_ = leanh::lean_ctor_get(v_x_1855_, 0);
            leanh::lean_inc(v_package_1865_);
            v_module_1866_ = leanh::lean_ctor_get(v_x_1855_, 1);
            leanh::lean_inc(v_module_1866_);
            leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1867_ = leanh::lean_apply_2(v_h__3_1858_, v_package_1865_, v_module_1866_);
            return v___x_1867_;
        }
        3 => {
            let mut v_package_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1860_);
            leanh::lean_dec(v_h__3_1858_);
            leanh::lean_dec(v_h__2_1857_);
            leanh::lean_dec(v_h__1_1856_);
            v_package_1868_ = leanh::lean_ctor_get(v_x_1855_, 0);
            leanh::lean_inc(v_package_1868_);
            v_target_1869_ = leanh::lean_ctor_get(v_x_1855_, 1);
            leanh::lean_inc(v_target_1869_);
            leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1870_ = leanh::lean_apply_2(v_h__4_1859_, v_package_1868_, v_target_1869_);
            return v___x_1870_;
        }
        _ => {
            let mut v_target_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1859_);
            leanh::lean_dec(v_h__3_1858_);
            leanh::lean_dec(v_h__2_1857_);
            leanh::lean_dec(v_h__1_1856_);
            v_target_1871_ = leanh::lean_ctor_get(v_x_1855_, 0);
            leanh::lean_inc_ref(v_target_1871_);
            v_facet_1872_ = leanh::lean_ctor_get(v_x_1855_, 1);
            leanh::lean_inc(v_facet_1872_);
            leanh::lean_dec_ref_known(v_x_1855_, 2);
            v___x_1873_ = leanh::lean_apply_2(v_h__5_1860_, v_target_1871_, v_facet_1872_);
            return v___x_1873_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_instReprBuildKey_repr_match__1_splitter(
    mut v_motive_1874_: *mut leanh::LeanObject,
    mut v_x_1875_: *mut leanh::LeanObject,
    mut v_h__1_1876_: *mut leanh::LeanObject,
    mut v_h__2_1877_: *mut leanh::LeanObject,
    mut v_h__3_1878_: *mut leanh::LeanObject,
    mut v_h__4_1879_: *mut leanh::LeanObject,
    mut v_h__5_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1875_) {
        0 => {
            let mut v_module_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1880_);
            leanh::lean_dec(v_h__4_1879_);
            leanh::lean_dec(v_h__3_1878_);
            leanh::lean_dec(v_h__2_1877_);
            v_module_1881_ = leanh::lean_ctor_get(v_x_1875_, 0);
            leanh::lean_inc(v_module_1881_);
            leanh::lean_dec_ref_known(v_x_1875_, 1);
            v___x_1882_ = leanh::lean_apply_1(v_h__1_1876_, v_module_1881_);
            return v___x_1882_;
        }
        1 => {
            let mut v_package_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1880_);
            leanh::lean_dec(v_h__4_1879_);
            leanh::lean_dec(v_h__3_1878_);
            leanh::lean_dec(v_h__1_1876_);
            v_package_1883_ = leanh::lean_ctor_get(v_x_1875_, 0);
            leanh::lean_inc(v_package_1883_);
            leanh::lean_dec_ref_known(v_x_1875_, 1);
            v___x_1884_ = leanh::lean_apply_1(v_h__2_1877_, v_package_1883_);
            return v___x_1884_;
        }
        2 => {
            let mut v_package_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1880_);
            leanh::lean_dec(v_h__4_1879_);
            leanh::lean_dec(v_h__2_1877_);
            leanh::lean_dec(v_h__1_1876_);
            v_package_1885_ = leanh::lean_ctor_get(v_x_1875_, 0);
            leanh::lean_inc(v_package_1885_);
            v_module_1886_ = leanh::lean_ctor_get(v_x_1875_, 1);
            leanh::lean_inc(v_module_1886_);
            leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1887_ = leanh::lean_apply_2(v_h__3_1878_, v_package_1885_, v_module_1886_);
            return v___x_1887_;
        }
        3 => {
            let mut v_package_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_1880_);
            leanh::lean_dec(v_h__3_1878_);
            leanh::lean_dec(v_h__2_1877_);
            leanh::lean_dec(v_h__1_1876_);
            v_package_1888_ = leanh::lean_ctor_get(v_x_1875_, 0);
            leanh::lean_inc(v_package_1888_);
            v_target_1889_ = leanh::lean_ctor_get(v_x_1875_, 1);
            leanh::lean_inc(v_target_1889_);
            leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1890_ = leanh::lean_apply_2(v_h__4_1879_, v_package_1888_, v_target_1889_);
            return v___x_1890_;
        }
        _ => {
            let mut v_target_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1879_);
            leanh::lean_dec(v_h__3_1878_);
            leanh::lean_dec(v_h__2_1877_);
            leanh::lean_dec(v_h__1_1876_);
            v_target_1891_ = leanh::lean_ctor_get(v_x_1875_, 0);
            leanh::lean_inc_ref(v_target_1891_);
            v_facet_1892_ = leanh::lean_ctor_get(v_x_1875_, 1);
            leanh::lean_inc(v_facet_1892_);
            leanh::lean_dec_ref_known(v_x_1875_, 2);
            v___x_1893_ = leanh::lean_apply_2(v_h__5_1880_, v_target_1891_, v_facet_1892_);
            return v___x_1893_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter___redArg(
    mut v_k_x27_1894_: *mut leanh::LeanObject,
    mut v_h__1_1895_: *mut leanh::LeanObject,
    mut v_h__2_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_k_x27_1894_) == 0 {
        let mut v_module_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1896_);
        v_module_1897_ = leanh::lean_ctor_get(v_k_x27_1894_, 0);
        leanh::lean_inc(v_module_1897_);
        leanh::lean_dec_ref_known(v_k_x27_1894_, 1);
        v___x_1898_ = leanh::lean_apply_1(v_h__1_1895_, v_module_1897_);
        return v___x_1898_;
    } else {
        let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1895_);
        v___x_1899_ =
            leanh::lean_apply_2(v_h__2_1896_, v_k_x27_1894_, leanh::lean_box(0));
        return v___x_1899_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__1_splitter(
    mut v_motive_1900_: *mut leanh::LeanObject,
    mut v_k_x27_1901_: *mut leanh::LeanObject,
    mut v_h__1_1902_: *mut leanh::LeanObject,
    mut v_h__2_1903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_k_x27_1901_) == 0 {
        let mut v_module_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1903_);
        v_module_1904_ = leanh::lean_ctor_get(v_k_x27_1901_, 0);
        leanh::lean_inc(v_module_1904_);
        leanh::lean_dec_ref_known(v_k_x27_1901_, 1);
        v___x_1905_ = leanh::lean_apply_1(v_h__1_1902_, v_module_1904_);
        return v___x_1905_;
    } else {
        let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1902_);
        v___x_1906_ =
            leanh::lean_apply_2(v_h__2_1903_, v_k_x27_1901_, leanh::lean_box(0));
        return v___x_1906_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter___redArg(
    mut v_k_x27_1907_: *mut leanh::LeanObject,
    mut v_h__1_1908_: *mut leanh::LeanObject,
    mut v_h__2_1909_: *mut leanh::LeanObject,
    mut v_h__3_1910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1907_) {
        0 => {
            let mut v_module_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1910_);
            leanh::lean_dec(v_h__2_1909_);
            v_module_1911_ = leanh::lean_ctor_get(v_k_x27_1907_, 0);
            leanh::lean_inc(v_module_1911_);
            leanh::lean_dec_ref_known(v_k_x27_1907_, 1);
            v___x_1912_ = leanh::lean_apply_1(v_h__1_1908_, v_module_1911_);
            return v___x_1912_;
        }
        1 => {
            let mut v_package_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1910_);
            leanh::lean_dec(v_h__1_1908_);
            v_package_1913_ = leanh::lean_ctor_get(v_k_x27_1907_, 0);
            leanh::lean_inc(v_package_1913_);
            leanh::lean_dec_ref_known(v_k_x27_1907_, 1);
            v___x_1914_ = leanh::lean_apply_1(v_h__2_1909_, v_package_1913_);
            return v___x_1914_;
        }
        _ => {
            let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1909_);
            leanh::lean_dec(v_h__1_1908_);
            v___x_1915_ = leanh::lean_apply_3(
                v_h__3_1910_,
                v_k_x27_1907_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1915_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__4_splitter(
    mut v_motive_1916_: *mut leanh::LeanObject,
    mut v_k_x27_1917_: *mut leanh::LeanObject,
    mut v_h__1_1918_: *mut leanh::LeanObject,
    mut v_h__2_1919_: *mut leanh::LeanObject,
    mut v_h__3_1920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1917_) {
        0 => {
            let mut v_module_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1920_);
            leanh::lean_dec(v_h__2_1919_);
            v_module_1921_ = leanh::lean_ctor_get(v_k_x27_1917_, 0);
            leanh::lean_inc(v_module_1921_);
            leanh::lean_dec_ref_known(v_k_x27_1917_, 1);
            v___x_1922_ = leanh::lean_apply_1(v_h__1_1918_, v_module_1921_);
            return v___x_1922_;
        }
        1 => {
            let mut v_package_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1920_);
            leanh::lean_dec(v_h__1_1918_);
            v_package_1923_ = leanh::lean_ctor_get(v_k_x27_1917_, 0);
            leanh::lean_inc(v_package_1923_);
            leanh::lean_dec_ref_known(v_k_x27_1917_, 1);
            v___x_1924_ = leanh::lean_apply_1(v_h__2_1919_, v_package_1923_);
            return v___x_1924_;
        }
        _ => {
            let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1919_);
            leanh::lean_dec(v_h__1_1918_);
            v___x_1925_ = leanh::lean_apply_3(
                v_h__3_1920_,
                v_k_x27_1917_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1925_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter___redArg(
    mut v_k_x27_1926_: *mut leanh::LeanObject,
    mut v_h__1_1927_: *mut leanh::LeanObject,
    mut v_h__2_1928_: *mut leanh::LeanObject,
    mut v_h__3_1929_: *mut leanh::LeanObject,
    mut v_h__4_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1926_) {
        4 => {
            let mut v_target_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1930_);
            leanh::lean_dec(v_h__3_1929_);
            leanh::lean_dec(v_h__2_1928_);
            v_target_1931_ = leanh::lean_ctor_get(v_k_x27_1926_, 0);
            leanh::lean_inc_ref(v_target_1931_);
            v_facet_1932_ = leanh::lean_ctor_get(v_k_x27_1926_, 1);
            leanh::lean_inc(v_facet_1932_);
            leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1933_ = leanh::lean_apply_2(v_h__1_1927_, v_target_1931_, v_facet_1932_);
            return v___x_1933_;
        }
        3 => {
            let mut v_package_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1930_);
            leanh::lean_dec(v_h__3_1929_);
            leanh::lean_dec(v_h__1_1927_);
            v_package_1934_ = leanh::lean_ctor_get(v_k_x27_1926_, 0);
            leanh::lean_inc(v_package_1934_);
            v_target_1935_ = leanh::lean_ctor_get(v_k_x27_1926_, 1);
            leanh::lean_inc(v_target_1935_);
            leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1936_ = leanh::lean_apply_2(v_h__2_1928_, v_package_1934_, v_target_1935_);
            return v___x_1936_;
        }
        2 => {
            let mut v_package_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1930_);
            leanh::lean_dec(v_h__2_1928_);
            leanh::lean_dec(v_h__1_1927_);
            v_package_1937_ = leanh::lean_ctor_get(v_k_x27_1926_, 0);
            leanh::lean_inc(v_package_1937_);
            v_module_1938_ = leanh::lean_ctor_get(v_k_x27_1926_, 1);
            leanh::lean_inc(v_module_1938_);
            leanh::lean_dec_ref_known(v_k_x27_1926_, 2);
            v___x_1939_ = leanh::lean_apply_2(v_h__3_1929_, v_package_1937_, v_module_1938_);
            return v___x_1939_;
        }
        _ => {
            let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1929_);
            leanh::lean_dec(v_h__2_1928_);
            leanh::lean_dec(v_h__1_1927_);
            v___x_1940_ = leanh::lean_apply_4(
                v_h__4_1930_,
                v_k_x27_1926_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1940_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__10_splitter(
    mut v_motive_1941_: *mut leanh::LeanObject,
    mut v_k_x27_1942_: *mut leanh::LeanObject,
    mut v_h__1_1943_: *mut leanh::LeanObject,
    mut v_h__2_1944_: *mut leanh::LeanObject,
    mut v_h__3_1945_: *mut leanh::LeanObject,
    mut v_h__4_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1942_) {
        4 => {
            let mut v_target_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1946_);
            leanh::lean_dec(v_h__3_1945_);
            leanh::lean_dec(v_h__2_1944_);
            v_target_1947_ = leanh::lean_ctor_get(v_k_x27_1942_, 0);
            leanh::lean_inc_ref(v_target_1947_);
            v_facet_1948_ = leanh::lean_ctor_get(v_k_x27_1942_, 1);
            leanh::lean_inc(v_facet_1948_);
            leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1949_ = leanh::lean_apply_2(v_h__1_1943_, v_target_1947_, v_facet_1948_);
            return v___x_1949_;
        }
        3 => {
            let mut v_package_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1946_);
            leanh::lean_dec(v_h__3_1945_);
            leanh::lean_dec(v_h__1_1943_);
            v_package_1950_ = leanh::lean_ctor_get(v_k_x27_1942_, 0);
            leanh::lean_inc(v_package_1950_);
            v_target_1951_ = leanh::lean_ctor_get(v_k_x27_1942_, 1);
            leanh::lean_inc(v_target_1951_);
            leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1952_ = leanh::lean_apply_2(v_h__2_1944_, v_package_1950_, v_target_1951_);
            return v___x_1952_;
        }
        2 => {
            let mut v_package_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_module_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1946_);
            leanh::lean_dec(v_h__2_1944_);
            leanh::lean_dec(v_h__1_1943_);
            v_package_1953_ = leanh::lean_ctor_get(v_k_x27_1942_, 0);
            leanh::lean_inc(v_package_1953_);
            v_module_1954_ = leanh::lean_ctor_get(v_k_x27_1942_, 1);
            leanh::lean_inc(v_module_1954_);
            leanh::lean_dec_ref_known(v_k_x27_1942_, 2);
            v___x_1955_ = leanh::lean_apply_2(v_h__3_1945_, v_package_1953_, v_module_1954_);
            return v___x_1955_;
        }
        _ => {
            let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1945_);
            leanh::lean_dec(v_h__2_1944_);
            leanh::lean_dec(v_h__1_1943_);
            v___x_1956_ = leanh::lean_apply_4(
                v_h__4_1946_,
                v_k_x27_1942_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1956_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(
    mut v_x_1957_: u8,
    mut v_h__1_1958_: *mut leanh::LeanObject,
    mut v_h__2_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1957_ == 1 {
        let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1959_);
        v___x_1960_ = leanh::lean_box(0);
        v___x_1961_ = leanh::lean_apply_1(v_h__1_1958_, v___x_1960_);
        return v___x_1961_;
    } else {
        let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1958_);
        v___x_1962_ = leanh::lean_box((v_x_1957_) as usize);
        v___x_1963_ =
            leanh::lean_apply_2(v_h__2_1959_, v___x_1962_, leanh::lean_box(0));
        return v___x_1963_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg___boxed(
    mut v_x_1964_: *mut leanh::LeanObject,
    mut v_h__1_1965_: *mut leanh::LeanObject,
    mut v_h__2_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_1967_: u8 = 0;
    let mut v_res_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1967_ = (leanh::lean_unbox(v_x_1964_) as u8);
    v_res_1968_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___redArg(
        v_x_17__boxed_1967_,
        v_h__1_1965_,
        v_h__2_1966_,
    );
    return v_res_1968_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(
    mut v_motive_1969_: *mut leanh::LeanObject,
    mut v_x_1970_: u8,
    mut v_h__1_1971_: *mut leanh::LeanObject,
    mut v_h__2_1972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1970_ == 1 {
        let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1972_);
        v___x_1973_ = leanh::lean_box(0);
        v___x_1974_ = leanh::lean_apply_1(v_h__1_1971_, v___x_1973_);
        return v___x_1974_;
    } else {
        let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1971_);
        v___x_1975_ = leanh::lean_box((v_x_1970_) as usize);
        v___x_1976_ =
            leanh::lean_apply_2(v_h__2_1972_, v___x_1975_, leanh::lean_box(0));
        return v___x_1976_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter___boxed(
    mut v_motive_1977_: *mut leanh::LeanObject,
    mut v_x_1978_: *mut leanh::LeanObject,
    mut v_h__1_1979_: *mut leanh::LeanObject,
    mut v_h__2_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_28__boxed_1981_: u8 = 0;
    let mut v_res_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_1981_ = (leanh::lean_unbox(v_x_1978_) as u8);
    v_res_1982_ = l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__7_splitter(
        v_motive_1977_,
        v_x_28__boxed_1981_,
        v_h__1_1979_,
        v_h__2_1980_,
    );
    return v_res_1982_;
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter___redArg(
    mut v_k_x27_1983_: *mut leanh::LeanObject,
    mut v_h__1_1984_: *mut leanh::LeanObject,
    mut v_h__2_1985_: *mut leanh::LeanObject,
    mut v_h__3_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1983_) {
        4 => {
            let mut v_target_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1986_);
            leanh::lean_dec(v_h__2_1985_);
            v_target_1987_ = leanh::lean_ctor_get(v_k_x27_1983_, 0);
            leanh::lean_inc_ref(v_target_1987_);
            v_facet_1988_ = leanh::lean_ctor_get(v_k_x27_1983_, 1);
            leanh::lean_inc(v_facet_1988_);
            leanh::lean_dec_ref_known(v_k_x27_1983_, 2);
            v___x_1989_ = leanh::lean_apply_2(v_h__1_1984_, v_target_1987_, v_facet_1988_);
            return v___x_1989_;
        }
        3 => {
            let mut v_package_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1986_);
            leanh::lean_dec(v_h__1_1984_);
            v_package_1990_ = leanh::lean_ctor_get(v_k_x27_1983_, 0);
            leanh::lean_inc(v_package_1990_);
            v_target_1991_ = leanh::lean_ctor_get(v_k_x27_1983_, 1);
            leanh::lean_inc(v_target_1991_);
            leanh::lean_dec_ref_known(v_k_x27_1983_, 2);
            v___x_1992_ = leanh::lean_apply_2(v_h__2_1985_, v_package_1990_, v_target_1991_);
            return v___x_1992_;
        }
        _ => {
            let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1985_);
            leanh::lean_dec(v_h__1_1984_);
            v___x_1993_ = leanh::lean_apply_3(
                v_h__3_1986_,
                v_k_x27_1983_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1993_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__13_splitter(
    mut v_motive_1994_: *mut leanh::LeanObject,
    mut v_k_x27_1995_: *mut leanh::LeanObject,
    mut v_h__1_1996_: *mut leanh::LeanObject,
    mut v_h__2_1997_: *mut leanh::LeanObject,
    mut v_h__3_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_k_x27_1995_) {
        4 => {
            let mut v_target_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_facet_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1998_);
            leanh::lean_dec(v_h__2_1997_);
            v_target_1999_ = leanh::lean_ctor_get(v_k_x27_1995_, 0);
            leanh::lean_inc_ref(v_target_1999_);
            v_facet_2000_ = leanh::lean_ctor_get(v_k_x27_1995_, 1);
            leanh::lean_inc(v_facet_2000_);
            leanh::lean_dec_ref_known(v_k_x27_1995_, 2);
            v___x_2001_ = leanh::lean_apply_2(v_h__1_1996_, v_target_1999_, v_facet_2000_);
            return v___x_2001_;
        }
        3 => {
            let mut v_package_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_target_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1998_);
            leanh::lean_dec(v_h__1_1996_);
            v_package_2002_ = leanh::lean_ctor_get(v_k_x27_1995_, 0);
            leanh::lean_inc(v_package_2002_);
            v_target_2003_ = leanh::lean_ctor_get(v_k_x27_1995_, 1);
            leanh::lean_inc(v_target_2003_);
            leanh::lean_dec_ref_known(v_k_x27_1995_, 2);
            v___x_2004_ = leanh::lean_apply_2(v_h__2_1997_, v_package_2002_, v_target_2003_);
            return v___x_2004_;
        }
        _ => {
            let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1997_);
            leanh::lean_dec(v_h__1_1996_);
            v___x_2005_ = leanh::lean_apply_3(
                v_h__3_1998_,
                v_k_x27_1995_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_2005_;
        }
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter___redArg(
    mut v_k_x27_2006_: *mut leanh::LeanObject,
    mut v_h__1_2007_: *mut leanh::LeanObject,
    mut v_h__2_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_k_x27_2006_) == 4 {
        let mut v_target_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_facet_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2008_);
        v_target_2009_ = leanh::lean_ctor_get(v_k_x27_2006_, 0);
        leanh::lean_inc_ref(v_target_2009_);
        v_facet_2010_ = leanh::lean_ctor_get(v_k_x27_2006_, 1);
        leanh::lean_inc(v_facet_2010_);
        leanh::lean_dec_ref_known(v_k_x27_2006_, 2);
        v___x_2011_ = leanh::lean_apply_2(v_h__1_2007_, v_target_2009_, v_facet_2010_);
        return v___x_2011_;
    } else {
        let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2007_);
        v___x_2012_ =
            leanh::lean_apply_2(v_h__2_2008_, v_k_x27_2006_, leanh::lean_box(0));
        return v___x_2012_;
    }
}
pub unsafe fn l___private_Lake_Build_Key_0__Lake_BuildKey_quickCmp_match__16_splitter(
    mut v_motive_2013_: *mut leanh::LeanObject,
    mut v_k_x27_2014_: *mut leanh::LeanObject,
    mut v_h__1_2015_: *mut leanh::LeanObject,
    mut v_h__2_2016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_k_x27_2014_) == 4 {
        let mut v_target_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_facet_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_2016_);
        v_target_2017_ = leanh::lean_ctor_get(v_k_x27_2014_, 0);
        leanh::lean_inc_ref(v_target_2017_);
        v_facet_2018_ = leanh::lean_ctor_get(v_k_x27_2014_, 1);
        leanh::lean_inc(v_facet_2018_);
        leanh::lean_dec_ref_known(v_k_x27_2014_, 2);
        v___x_2019_ = leanh::lean_apply_2(v_h__1_2015_, v_target_2017_, v_facet_2018_);
        return v___x_2019_;
    } else {
        let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_2015_);
        v___x_2020_ =
            leanh::lean_apply_2(v_h__2_2016_, v_k_x27_2014_, leanh::lean_box(0));
        return v___x_2020_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Build_Key(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Build_Key(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Build_Key(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lake_Util_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Build_Key(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Build_Key(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Build_Key(builtin);
}