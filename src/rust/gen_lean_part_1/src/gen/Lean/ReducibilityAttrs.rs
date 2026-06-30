// Lean compiler output
// Module: Lean.ReducibilityAttrs
// Imports: Lean.ScopedEnvExtension
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_uget_borrowed,
    lean_array_uset, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_shiftr,
    lean_nat_sub, lean_nat_to_int, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_quickLt};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, lean_register_option};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::SMap::l_Lean_SMap_instInhabited;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_isDefinition;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_addEntry___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
pub static mut l_Lean_instInhabitedReducibilityStatus_default: u8 = 0;
pub static mut l_Lean_instInhabitedReducibilityStatus: u8 = 0;
pub static l_Lean_instReprReducibilityStatus_repr___closed__0_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116, 97,
        116, 117, 115, 46, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__1_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__2_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116, 97,
        116, 117, 115, 46, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__3_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__4_value:
    leanh::LeanStringObject<36> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116, 97,
        116, 117, 115, 46, 105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__5_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__6_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116, 97,
        116, 117, 115, 46, 105, 109, 112, 108, 105, 99, 105, 116, 82, 101, 100, 117, 99, 105, 98,
        108, 101, 0,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__7_value: leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprReducibilityStatus_repr___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprReducibilityStatus_repr___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprReducibilityStatus___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprReducibilityStatus_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprReducibilityStatus___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprReducibilityStatus: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instBEqReducibilityStatus___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqReducibilityStatus_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqReducibilityStatus___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqReducibilityStatus: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__0_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [91, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 0],
};
static mut l_Lean_ReducibilityStatus_toAttrString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__1_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
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
        91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 0,
    ],
};
static mut l_Lean_ReducibilityStatus_toAttrString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        91, 105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 0,
    ],
};
static mut l_Lean_ReducibilityStatus_toAttrString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__3_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
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
        91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101,
        93, 0,
    ],
};
static mut l_Lean_ReducibilityStatus_toAttrString___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 111, 114, 101, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116, 114, 105, 101, 115, 58, 32, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 67, 111, 114, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12246743371341285727 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [1 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<8> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_reducibilityCoreExt: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13965638932435844466 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_reducibilityExtraExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_getReducibilityStatusCore___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getReducibilityStatusCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getReducibilityStatusCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_getReducibilityStatusCore___closed__1_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getReducibilityStatusCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_getReducibilityStatusCore___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_getReducibilityStatusCore___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_getReducibilityStatusCore___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [97, 108, 108, 111, 119, 85, 110, 115, 97, 102, 101, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,1642828907576623915 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanStringObject<235> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 235, m_capacity: 235, m_length: 234, m_data: [101, 110, 97, 98, 108, 101, 115, 32, 117, 115, 101, 114, 115, 32, 116, 111, 32, 109, 111, 100, 105, 102, 121, 32, 116, 104, 101, 32, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 32, 115, 101, 116, 116, 105, 110, 103, 115, 32, 102, 111, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 101, 118, 101, 110, 32, 119, 104, 101, 110, 32, 115, 117, 99, 104, 32, 99, 104, 97, 110, 103, 101, 115, 32, 97, 114, 101, 32, 100, 101, 101, 109, 101, 100, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 32, 104, 97, 122, 97, 114, 100, 111, 117, 115, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 115, 105, 109, 112, 96, 32, 97, 110, 100, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 32, 114, 101, 115, 111, 108, 117, 116, 105, 111, 110, 32, 109, 97, 105, 110, 116, 97, 105, 110, 32, 116, 101, 114, 109, 32, 105, 110, 100, 105, 99, 101, 115, 32, 119, 104, 101, 114, 101, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32, 101, 120, 112, 97, 110, 100, 101, 100, 46, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,681850948520615530 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject;
pub static mut l_Lean_allowUnsafeReducibility: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value:
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
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 114, 101, 100,
        117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value:
    leanh::LeanStringObject<44> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 44,
    m_capacity: 44,
    m_length: 43,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32,
        96, 91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 98,
        117, 116, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value:
    leanh::LeanStringObject<38> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 115, 101, 109,
        105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value:
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
        96, 44, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32,
        96, 91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 98, 121,
        32, 100, 101, 102, 97, 117, 108, 116, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 105, 114, 114,
        101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value:
    leanh::LeanStringObject<71> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32,
        96, 91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 110,
        111, 114, 32, 96, 91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99,
        105, 98, 108, 101, 93, 96, 44, 32, 98, 117, 116, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 105, 109, 112,
        108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 96,
        0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 114, 101, 100, 117, 99,
        105, 98, 105, 108, 105, 116, 121, 32, 115, 116, 97, 116, 117, 115, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value:
    leanh::LeanStringObject<73> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 73,
    m_capacity: 73,
    m_length: 72,
    m_data: [
        96, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 100, 101, 102, 105,
        110, 101, 100, 32, 105, 110, 32, 116, 104, 105, 115, 32, 102, 105, 108, 101, 44, 32, 99,
        111, 110, 115, 105, 100, 101, 114, 32, 117, 115, 105, 110, 103, 32, 116, 104, 101, 32, 96,
        108, 111, 99, 97, 108, 96, 32, 109, 111, 100, 105, 102, 105, 101, 114, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 108, 111, 99, 97,
        108, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value:
    leanh::LeanStringObject<111> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 111,
    m_capacity: 111,
    m_length: 110,
    m_data: [
        96, 44, 32, 114, 101, 99, 97, 108, 108, 32, 116, 104, 97, 116, 32, 96, 91, 114, 101, 100,
        117, 99, 105, 98, 108, 101, 93, 96, 32, 97, 102, 102, 101, 99, 116, 115, 32, 116, 104, 101,
        32, 116, 101, 114, 109, 32, 105, 110, 100, 101, 120, 105, 110, 103, 32, 100, 97, 116, 97,
        115, 116, 114, 117, 99, 116, 117, 114, 101, 115, 32, 117, 115, 101, 100, 32, 98, 121, 32,
        96, 115, 105, 109, 112, 96, 32, 97, 110, 100, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115,
        115, 32, 114, 101, 115, 111, 108, 117, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 108, 111, 99, 97,
        108, 32, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 96,
        0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value:
    leanh::LeanStringObject<17> = leanh::LeanStringObject {
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
        96, 32, 105, 115, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
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
        96, 44, 32, 96, 91, 105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 32, 101,
        120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 108, 111, 99, 97,
        108, 32, 105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value:
    leanh::LeanStringObject<57> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        96, 44, 32, 96, 91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96,
        32, 110, 111, 114, 32, 96, 91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100,
        117, 99, 105, 98, 108, 101, 93, 96, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value:
    leanh::LeanStringObject<46> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 46,
    m_capacity: 46,
    m_length: 45,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 96, 91, 108, 111, 99, 97,
        108, 32, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108,
        101, 93, 96, 44, 32, 96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value:
    leanh::LeanStringObject<30> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        96, 44, 32, 96, 91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 96,
        32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 115, 101, 116, 32, 114, 101, 100, 117, 99,
        105, 98, 105, 108, 105, 116, 121, 32, 115, 116, 97, 116, 117, 115, 32, 102, 111, 114, 32,
        96, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value:
    leanh::LeanStringObject<71> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 71,
    m_capacity: 71,
    m_length: 70,
    m_data: [
        96, 44, 32, 116, 104, 101, 32, 96, 115, 99, 111, 112, 101, 100, 96, 32, 109, 111, 100, 105,
        102, 105, 101, 114, 32, 105, 115, 32, 110, 111, 116, 32, 114, 101, 99, 111, 109, 109, 101,
        110, 100, 101, 100, 32, 102, 111, 114, 32, 116, 104, 105, 115, 32, 107, 105, 110, 100, 32,
        111, 102, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value:
    leanh::LeanStringObject<22> = leanh::LeanStringObject {
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
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105,
        111, 110, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value:
    leanh::LeanStringObject<89> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 89,
    m_capacity: 89,
    m_length: 88,
    m_data: [
        85, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 97, 108, 108,
        111, 119, 85, 110, 115, 97, 102, 101, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116,
        121, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 111, 118, 101, 114, 114, 105, 100, 101,
        32, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 32, 115, 116, 97, 116, 117,
        115, 32, 118, 97, 108, 105, 100, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value:
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
        l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value)
        as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 65, 116, 116, 114, 115, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16674771574477616125 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,8591613141613872776 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,535016304756014689 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12932279219522036888 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1194659137222478697 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut leanh::LeanObject,8790433524930448172 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12136383179595628843 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 562565324 as usize) << 1) | 1) as *mut leanh::LeanObject,74207542672438541 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5664183133159884526 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2546798191073904962 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,12674079943837901979 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6878064079637565245 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject,7045040058828669725 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2616510057874194026 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 448179520 as usize) << 1) | 1) as *mut leanh::LeanObject,8351696710712280576 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6815184137236015063 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17909152065865606463 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,9821775911497995642 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11290700302157177994 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanStringObject<31> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 3 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 598760241 as usize) << 1) | 1) as *mut leanh::LeanObject,13228617787602902987 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17949311112788899376 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10027910081678967092 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,11004149243798455437 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1015365147026633853 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [97, 108, 105, 97, 115, 32, 102, 111, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,0 as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_ReducibilityStatus_ctorIdx(
    mut v_x_2474_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2474_ {
        0 => {
            let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2475_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2475_;
        }
        1 => {
            let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2476_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2476_;
        }
        2 => {
            let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2477_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2477_;
        }
        _ => {
            let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2478_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2478_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorIdx___boxed(
    mut v_x_2479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_2480_: u8 = 0;
    let mut v_res_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2480_ = (leanh::lean_unbox(v_x_2479_) as u8);
    v_res_2481_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_boxed_2480_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toCtorIdx(
    mut v_x_2482_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2483_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toCtorIdx___boxed(
    mut v_x_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_2485_: u8 = 0;
    let mut v_res_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2485_ = (leanh::lean_unbox(v_x_2484_) as u8);
    v_res_2486_ = l_Lean_ReducibilityStatus_toCtorIdx(v_x_4__boxed_2485_);
    return v_res_2486_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___redArg(
    mut v_k_2487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2487_);
    return v_k_2487_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(
    mut v_k_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Lean_ReducibilityStatus_ctorElim___redArg(v_k_2488_);
    leanh::lean_dec(v_k_2488_);
    return v_res_2489_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim(
    mut v_motive_2490_: *mut leanh::LeanObject,
    mut v_ctorIdx_2491_: *mut leanh::LeanObject,
    mut v_t_2492_: u8,
    mut v_h_2493_: *mut leanh::LeanObject,
    mut v_k_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_2494_);
    return v_k_2494_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___boxed(
    mut v_motive_2495_: *mut leanh::LeanObject,
    mut v_ctorIdx_2496_: *mut leanh::LeanObject,
    mut v_t_2497_: *mut leanh::LeanObject,
    mut v_h_2498_: *mut leanh::LeanObject,
    mut v_k_2499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2500_: u8 = 0;
    let mut v_res_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2500_ = (leanh::lean_unbox(v_t_2497_) as u8);
    v_res_2501_ = l_Lean_ReducibilityStatus_ctorElim(
        v_motive_2495_,
        v_ctorIdx_2496_,
        v_t_boxed_2500_,
        v_h_2498_,
        v_k_2499_,
    );
    leanh::lean_dec(v_k_2499_);
    leanh::lean_dec(v_ctorIdx_2496_);
    return v_res_2501_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___redArg(
    mut v_reducible_2502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reducible_2502_);
    return v_reducible_2502_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(
    mut v_reducible_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2504_ = l_Lean_ReducibilityStatus_reducible_elim___redArg(v_reducible_2503_);
    leanh::lean_dec(v_reducible_2503_);
    return v_res_2504_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim(
    mut v_motive_2505_: *mut leanh::LeanObject,
    mut v_t_2506_: u8,
    mut v_h_2507_: *mut leanh::LeanObject,
    mut v_reducible_2508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_reducible_2508_);
    return v_reducible_2508_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___boxed(
    mut v_motive_2509_: *mut leanh::LeanObject,
    mut v_t_2510_: *mut leanh::LeanObject,
    mut v_h_2511_: *mut leanh::LeanObject,
    mut v_reducible_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2513_: u8 = 0;
    let mut v_res_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2513_ = (leanh::lean_unbox(v_t_2510_) as u8);
    v_res_2514_ = l_Lean_ReducibilityStatus_reducible_elim(
        v_motive_2509_,
        v_t_boxed_2513_,
        v_h_2511_,
        v_reducible_2512_,
    );
    leanh::lean_dec(v_reducible_2512_);
    return v_res_2514_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___redArg(
    mut v_semireducible_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_semireducible_2515_);
    return v_semireducible_2515_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(
    mut v_semireducible_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2517_ = l_Lean_ReducibilityStatus_semireducible_elim___redArg(v_semireducible_2516_);
    leanh::lean_dec(v_semireducible_2516_);
    return v_res_2517_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim(
    mut v_motive_2518_: *mut leanh::LeanObject,
    mut v_t_2519_: u8,
    mut v_h_2520_: *mut leanh::LeanObject,
    mut v_semireducible_2521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_semireducible_2521_);
    return v_semireducible_2521_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___boxed(
    mut v_motive_2522_: *mut leanh::LeanObject,
    mut v_t_2523_: *mut leanh::LeanObject,
    mut v_h_2524_: *mut leanh::LeanObject,
    mut v_semireducible_2525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2526_: u8 = 0;
    let mut v_res_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2526_ = (leanh::lean_unbox(v_t_2523_) as u8);
    v_res_2527_ = l_Lean_ReducibilityStatus_semireducible_elim(
        v_motive_2522_,
        v_t_boxed_2526_,
        v_h_2524_,
        v_semireducible_2525_,
    );
    leanh::lean_dec(v_semireducible_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___redArg(
    mut v_irreducible_2528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_irreducible_2528_);
    return v_irreducible_2528_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(
    mut v_irreducible_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_ReducibilityStatus_irreducible_elim___redArg(v_irreducible_2529_);
    leanh::lean_dec(v_irreducible_2529_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim(
    mut v_motive_2531_: *mut leanh::LeanObject,
    mut v_t_2532_: u8,
    mut v_h_2533_: *mut leanh::LeanObject,
    mut v_irreducible_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_irreducible_2534_);
    return v_irreducible_2534_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___boxed(
    mut v_motive_2535_: *mut leanh::LeanObject,
    mut v_t_2536_: *mut leanh::LeanObject,
    mut v_h_2537_: *mut leanh::LeanObject,
    mut v_irreducible_2538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2539_: u8 = 0;
    let mut v_res_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2539_ = (leanh::lean_unbox(v_t_2536_) as u8);
    v_res_2540_ = l_Lean_ReducibilityStatus_irreducible_elim(
        v_motive_2535_,
        v_t_boxed_2539_,
        v_h_2537_,
        v_irreducible_2538_,
    );
    leanh::lean_dec(v_irreducible_2538_);
    return v_res_2540_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(
    mut v_implicitReducible_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_implicitReducible_2541_);
    return v_implicitReducible_2541_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(
    mut v_implicitReducible_2542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2543_ =
        l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(v_implicitReducible_2542_);
    leanh::lean_dec(v_implicitReducible_2542_);
    return v_res_2543_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim(
    mut v_motive_2544_: *mut leanh::LeanObject,
    mut v_t_2545_: u8,
    mut v_h_2546_: *mut leanh::LeanObject,
    mut v_implicitReducible_2547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_implicitReducible_2547_);
    return v_implicitReducible_2547_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(
    mut v_motive_2548_: *mut leanh::LeanObject,
    mut v_t_2549_: *mut leanh::LeanObject,
    mut v_h_2550_: *mut leanh::LeanObject,
    mut v_implicitReducible_2551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_2552_ = (leanh::lean_unbox(v_t_2549_) as u8);
    v_res_2553_ = l_Lean_ReducibilityStatus_implicitReducible_elim(
        v_motive_2548_,
        v_t_boxed_2552_,
        v_h_2550_,
        v_implicitReducible_2551_,
    );
    leanh::lean_dec(v_implicitReducible_2551_);
    return v_res_2553_;
}
pub unsafe fn _init_l_Lean_instInhabitedReducibilityStatus_default() -> u8 {
    let mut v___x_2554_: u8 = 0;
    v___x_2554_ = 0;
    return v___x_2554_;
}
pub unsafe fn _init_l_Lean_instInhabitedReducibilityStatus() -> u8 {
    let mut v___x_2555_: u8 = 0;
    v___x_2555_ = 0;
    return v___x_2555_;
}
pub unsafe fn _init_l_Lean_instReprReducibilityStatus_repr___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2568_ = leanh::lean_unsigned_to_nat(2);
    v___x_2569_ = lean_nat_to_int(v___x_2568_);
    return v___x_2569_;
}
pub unsafe fn _init_l_Lean_instReprReducibilityStatus_repr___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2570_ = leanh::lean_unsigned_to_nat(1);
    v___x_2571_ = lean_nat_to_int(v___x_2570_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_instReprReducibilityStatus_repr(
    mut v_x_2572_: u8,
    mut v_prec_2573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: u8 = 0;
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: u8 = 0;
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2572_ {
                0 => {
                    v___x_2602_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2603_ = lean_nat_dec_le(v___x_2602_, v_prec_2573_);
                    if v___x_2603_ == 0 {
                        v___x_2604_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__8,
                        );
                        v___y_2575_ = v___x_2604_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2605_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__9,
                        );
                        v___y_2575_ = v___x_2605_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2606_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2607_ = lean_nat_dec_le(v___x_2606_, v_prec_2573_);
                    if v___x_2607_ == 0 {
                        v___x_2608_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__8,
                        );
                        v___y_2582_ = v___x_2608_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2609_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__9,
                        );
                        v___y_2582_ = v___x_2609_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v___x_2610_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2611_ = lean_nat_dec_le(v___x_2610_, v_prec_2573_);
                    if v___x_2611_ == 0 {
                        v___x_2612_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__8,
                        );
                        v___y_2589_ = v___x_2612_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2613_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__9,
                        );
                        v___y_2589_ = v___x_2613_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_2614_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2615_ = lean_nat_dec_le(v___x_2614_, v_prec_2573_);
                    if v___x_2615_ == 0 {
                        v___x_2616_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__8_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__8,
                        );
                        v___y_2596_ = v___x_2616_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2617_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_instReprReducibilityStatus_repr___closed__9_once
                            ),
                            _init_l_Lean_instReprReducibilityStatus_repr___closed__9,
                        );
                        v___y_2596_ = v___x_2617_;
                        state = 4;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2576_ = l_Lean_instReprReducibilityStatus_repr___closed__1;
                leanh::lean_inc(v___y_2575_);
                v___x_2577_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2577_, 0, v___y_2575_);
                leanh::lean_ctor_set(v___x_2577_, 1, v___x_2576_);
                v___x_2578_ = 0;
                v___x_2579_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2579_, 0, v___x_2577_);
                leanh::lean_ctor_set_uint8(
                    v___x_2579_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2578_,
                );
                v___x_2580_ = l_Repr_addAppParen(v___x_2579_, v_prec_2573_);
                return v___x_2580_;
            }
            2 => {
                v___x_2583_ = l_Lean_instReprReducibilityStatus_repr___closed__3;
                leanh::lean_inc(v___y_2582_);
                v___x_2584_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2584_, 0, v___y_2582_);
                leanh::lean_ctor_set(v___x_2584_, 1, v___x_2583_);
                v___x_2585_ = 0;
                v___x_2586_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2586_, 0, v___x_2584_);
                leanh::lean_ctor_set_uint8(
                    v___x_2586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2585_,
                );
                v___x_2587_ = l_Repr_addAppParen(v___x_2586_, v_prec_2573_);
                return v___x_2587_;
            }
            3 => {
                v___x_2590_ = l_Lean_instReprReducibilityStatus_repr___closed__5;
                leanh::lean_inc(v___y_2589_);
                v___x_2591_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2591_, 0, v___y_2589_);
                leanh::lean_ctor_set(v___x_2591_, 1, v___x_2590_);
                v___x_2592_ = 0;
                v___x_2593_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2593_, 0, v___x_2591_);
                leanh::lean_ctor_set_uint8(
                    v___x_2593_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2592_,
                );
                v___x_2594_ = l_Repr_addAppParen(v___x_2593_, v_prec_2573_);
                return v___x_2594_;
            }
            4 => {
                v___x_2597_ = l_Lean_instReprReducibilityStatus_repr___closed__7;
                leanh::lean_inc(v___y_2596_);
                v___x_2598_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2598_, 0, v___y_2596_);
                leanh::lean_ctor_set(v___x_2598_, 1, v___x_2597_);
                v___x_2599_ = 0;
                v___x_2600_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                leanh::lean_ctor_set_uint8(
                    v___x_2600_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2599_,
                );
                v___x_2601_ = l_Repr_addAppParen(v___x_2600_, v_prec_2573_);
                return v___x_2601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprReducibilityStatus_repr___boxed(
    mut v_x_2618_: *mut leanh::LeanObject,
    mut v_prec_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_233__boxed_2620_: u8 = 0;
    let mut v_res_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_233__boxed_2620_ = (leanh::lean_unbox(v_x_2618_) as u8);
    v_res_2621_ = l_Lean_instReprReducibilityStatus_repr(v_x_233__boxed_2620_, v_prec_2619_);
    leanh::lean_dec(v_prec_2619_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_instBEqReducibilityStatus_beq(mut v_x_2624_: u8, mut v_y_2625_: u8) -> u8 {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    v___x_2626_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_2624_);
    v___x_2627_ = l_Lean_ReducibilityStatus_ctorIdx(v_y_2625_);
    v___x_2628_ = lean_nat_dec_eq(v___x_2626_, v___x_2627_);
    leanh::lean_dec(v___x_2627_);
    leanh::lean_dec(v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn l_Lean_instBEqReducibilityStatus_beq___boxed(
    mut v_x_2629_: *mut leanh::LeanObject,
    mut v_y_2630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_2631_: u8 = 0;
    let mut v_y_18__boxed_2632_: u8 = 0;
    let mut v_res_2633_: u8 = 0;
    let mut v_r_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2631_ = (leanh::lean_unbox(v_x_2629_) as u8);
    v_y_18__boxed_2632_ = (leanh::lean_unbox(v_y_2630_) as u8);
    v_res_2633_ = l_Lean_instBEqReducibilityStatus_beq(v_x_17__boxed_2631_, v_y_18__boxed_2632_);
    v_r_2634_ = leanh::lean_box((v_res_2633_) as usize);
    return v_r_2634_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toAttrString(
    mut v_x_2641_: u8,
) -> *mut leanh::LeanObject {
    match v_x_2641_ {
        0 => {
            let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2642_ = l_Lean_ReducibilityStatus_toAttrString___closed__0;
            return v___x_2642_;
        }
        1 => {
            let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2643_ = l_Lean_ReducibilityStatus_toAttrString___closed__1;
            return v___x_2643_;
        }
        2 => {
            let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2644_ = l_Lean_ReducibilityStatus_toAttrString___closed__2;
            return v___x_2644_;
        }
        _ => {
            let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2645_ = l_Lean_ReducibilityStatus_toAttrString___closed__3;
            return v___x_2645_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityStatus_toAttrString___boxed(
    mut v_x_2646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_40__boxed_2647_: u8 = 0;
    let mut v_res_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_2647_ = (leanh::lean_unbox(v_x_2646_) as u8);
    v_res_2648_ = l_Lean_ReducibilityStatus_toAttrString(v_x_40__boxed_2647_);
    return v_res_2648_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_s_2649_: *mut leanh::LeanObject,
    mut v_p_2650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2651_ = leanh::lean_ctor_get(v_p_2650_, 0);
    leanh::lean_inc(v_fst_2651_);
    v_snd_2652_ = leanh::lean_ctor_get(v_p_2650_, 1);
    leanh::lean_inc(v_snd_2652_);
    leanh::lean_dec_ref(v_p_2650_);
    v___x_2653_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_2651_,
        v_snd_2652_,
        v_s_2649_,
    );
    return v___x_2653_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_2654_: *mut leanh::LeanObject,
    mut v_x_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2655_) == 0 {
                    v_k_2656_ = leanh::lean_ctor_get(v_x_2655_, 1);
                    v_v_2657_ = leanh::lean_ctor_get(v_x_2655_, 2);
                    v_l_2658_ = leanh::lean_ctor_get(v_x_2655_, 3);
                    v_r_2659_ = leanh::lean_ctor_get(v_x_2655_, 4);
                    v___x_2660_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2654_, v_l_2658_);
                    leanh::lean_inc(v_v_2657_);
                    leanh::lean_inc(v_k_2656_);
                    v___x_2661_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2661_, 0, v_k_2656_);
                    leanh::lean_ctor_set(v___x_2661_, 1, v_v_2657_);
                    v___x_2662_ = lean_array_push(v___x_2660_, v___x_2661_);
                    v_init_2654_ = v___x_2662_;
                    v_x_2655_ = v_r_2659_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2654_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_2664_: *mut leanh::LeanObject,
    mut v_x_2665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2666_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2664_, v_x_2665_);
    leanh::lean_dec(v_x_2665_);
    return v_res_2666_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_b_2668_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    v_fst_2669_ = leanh::lean_ctor_get(v_a_2667_, 0);
    v_fst_2670_ = leanh::lean_ctor_get(v_b_2668_, 0);
    v___x_2671_ = l_Lean_Name_quickLt(v_fst_2669_, v_fst_2670_);
    return v___x_2671_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_b_2673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2674_: u8 = 0;
    let mut v_r_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2672_, v_b_2673_);
    leanh::lean_dec_ref(v_b_2673_);
    leanh::lean_dec_ref(v_a_2672_);
    v_r_2675_ = leanh::lean_box((v_res_2674_) as usize);
    return v_r_2675_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_hi_2676_: *mut leanh::LeanObject,
    mut v_pivot_2677_: *mut leanh::LeanObject,
    mut v_as_2678_: *mut leanh::LeanObject,
    mut v_i_2679_: *mut leanh::LeanObject,
    mut v_k_2680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2681_ = lean_nat_dec_lt(v_k_2680_, v_hi_2676_);
                if v___x_2681_ == 0 {
                    leanh::lean_dec(v_k_2680_);
                    v___x_2682_ = lean_array_fswap(v_as_2678_, v_i_2679_, v_hi_2676_);
                    v___x_2683_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2683_, 0, v_i_2679_);
                    leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                    return v___x_2683_;
                } else {
                    v___x_2684_ = lean_array_fget_borrowed(v_as_2678_, v_k_2680_);
                    v_fst_2685_ = leanh::lean_ctor_get(v___x_2684_, 0);
                    v_fst_2686_ = leanh::lean_ctor_get(v_pivot_2677_, 0);
                    v___x_2687_ = l_Lean_Name_quickLt(v_fst_2685_, v_fst_2686_);
                    if v___x_2687_ == 0 {
                        v___x_2688_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2689_ = lean_nat_add(v_k_2680_, v___x_2688_);
                        leanh::lean_dec(v_k_2680_);
                        v_k_2680_ = v___x_2689_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2691_ = lean_array_fswap(v_as_2678_, v_i_2679_, v_k_2680_);
                        v___x_2692_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2693_ = lean_nat_add(v_i_2679_, v___x_2692_);
                        leanh::lean_dec(v_i_2679_);
                        v___x_2694_ = lean_nat_add(v_k_2680_, v___x_2692_);
                        leanh::lean_dec(v_k_2680_);
                        v_as_2678_ = v___x_2691_;
                        v_i_2679_ = v___x_2693_;
                        v_k_2680_ = v___x_2694_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_hi_2696_: *mut leanh::LeanObject,
    mut v_pivot_2697_: *mut leanh::LeanObject,
    mut v_as_2698_: *mut leanh::LeanObject,
    mut v_i_2699_: *mut leanh::LeanObject,
    mut v_k_2700_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2696_, v_pivot_2697_, v_as_2698_, v_i_2699_, v_k_2700_);
    leanh::lean_dec_ref(v_pivot_2697_);
    leanh::lean_dec(v_hi_2696_);
    return v_res_2701_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(
    mut v_n_2702_: *mut leanh::LeanObject,
    mut v_as_2703_: *mut leanh::LeanObject,
    mut v_lo_2704_: *mut leanh::LeanObject,
    mut v_hi_2705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2717_ = lean_nat_dec_lt(v_lo_2704_, v_hi_2705_);
                if v___x_2717_ == 0 {
                    leanh::lean_dec(v_lo_2704_);
                    return v_as_2703_;
                } else {
                    v___x_2718_ = lean_nat_add(v_lo_2704_, v_hi_2705_);
                    v___x_2719_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_2720_ = lean_nat_shiftr(v___x_2718_, v___x_2719_);
                    leanh::lean_dec(v___x_2718_);
                    v___x_2733_ = lean_array_fget_borrowed(v_as_2703_, v_mid_2720_);
                    v___x_2734_ = lean_array_fget_borrowed(v_as_2703_, v_lo_2704_);
                    v___x_2735_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2733_, v___x_2734_);
                    if v___x_2735_ == 0 {
                        v___y_2728_ = v_as_2703_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2736_ = lean_array_fswap(v_as_2703_, v_lo_2704_, v_mid_2720_);
                        v___y_2728_ = v___x_2736_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2708_ = lean_array_fget(v___y_2707_, v_hi_2705_);
                leanh::lean_inc_n(v_lo_2704_, 2);
                v___x_2709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2705_, v_pivot_2708_, v___y_2707_, v_lo_2704_, v_lo_2704_);
                leanh::lean_dec(v_pivot_2708_);
                v_fst_2710_ = leanh::lean_ctor_get(v___x_2709_, 0);
                leanh::lean_inc(v_fst_2710_);
                v_snd_2711_ = leanh::lean_ctor_get(v___x_2709_, 1);
                leanh::lean_inc(v_snd_2711_);
                leanh::lean_dec_ref(v___x_2709_);
                v___x_2712_ = lean_nat_dec_le(v_hi_2705_, v_fst_2710_);
                if v___x_2712_ == 0 {
                    v___x_2713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2702_, v_snd_2711_, v_lo_2704_, v_fst_2710_);
                    v___x_2714_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2715_ = lean_nat_add(v_fst_2710_, v___x_2714_);
                    leanh::lean_dec(v_fst_2710_);
                    v_as_2703_ = v___x_2713_;
                    v_lo_2704_ = v___x_2715_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2710_);
                    leanh::lean_dec(v_lo_2704_);
                    return v_snd_2711_;
                }
            }
            2 => {
                v___x_2723_ = lean_array_fget_borrowed(v___y_2722_, v_mid_2720_);
                v___x_2724_ = lean_array_fget_borrowed(v___y_2722_, v_hi_2705_);
                v___x_2725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2723_, v___x_2724_);
                if v___x_2725_ == 0 {
                    leanh::lean_dec(v_mid_2720_);
                    v___y_2707_ = v___y_2722_;
                    state = 1;
                    continue;
                } else {
                    v___x_2726_ = lean_array_fswap(v___y_2722_, v_mid_2720_, v_hi_2705_);
                    leanh::lean_dec(v_mid_2720_);
                    v___y_2707_ = v___x_2726_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2729_ = lean_array_fget_borrowed(v___y_2728_, v_hi_2705_);
                v___x_2730_ = lean_array_fget_borrowed(v___y_2728_, v_lo_2704_);
                v___x_2731_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2729_, v___x_2730_);
                if v___x_2731_ == 0 {
                    v___y_2722_ = v___y_2728_;
                    state = 2;
                    continue;
                } else {
                    v___x_2732_ = lean_array_fswap(v___y_2728_, v_lo_2704_, v_hi_2705_);
                    v___y_2722_ = v___x_2732_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_n_2737_: *mut leanh::LeanObject,
    mut v_as_2738_: *mut leanh::LeanObject,
    mut v_lo_2739_: *mut leanh::LeanObject,
    mut v_hi_2740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2737_, v_as_2738_, v_lo_2739_, v_hi_2740_);
    leanh::lean_dec(v_hi_2740_);
    leanh::lean_dec(v_n_2737_);
    return v_res_2741_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_x_2744_: *mut leanh::LeanObject,
    mut v_s_2745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = leanh::lean_unsigned_to_nat(0);
                v___x_2747_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                v_r_2748_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_2747_, v_s_2745_);
                v___x_2749_ = lean_array_get_size(v_r_2748_);
                v___x_2755_ = lean_nat_dec_eq(v___x_2749_, v___x_2746_);
                if v___x_2755_ == 0 {
                    v___x_2756_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2757_ = lean_nat_sub(v___x_2749_, v___x_2756_);
                    v___x_2761_ = lean_nat_dec_le(v___x_2746_, v___x_2757_);
                    if v___x_2761_ == 0 {
                        leanh::lean_inc(v___x_2757_);
                        v___y_2759_ = v___x_2757_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2759_ = v___x_2746_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref_n(v_r_2748_, 2);
                    v___x_2762_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2762_, 0, v_r_2748_);
                    leanh::lean_ctor_set(v___x_2762_, 1, v_r_2748_);
                    leanh::lean_ctor_set(v___x_2762_, 2, v_r_2748_);
                    return v___x_2762_;
                }
            }
            1 => {
                v___x_2753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2749_, v_r_2748_, v___y_2751_, v___y_2752_);
                leanh::lean_dec(v___y_2752_);
                leanh::lean_inc_ref_n(v___x_2753_, 2);
                v___x_2754_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                leanh::lean_ctor_set(v___x_2754_, 1, v___x_2753_);
                leanh::lean_ctor_set(v___x_2754_, 2, v___x_2753_);
                return v___x_2754_;
            }
            2 => {
                v___x_2760_ = lean_nat_dec_le(v___y_2759_, v___x_2757_);
                if v___x_2760_ == 0 {
                    leanh::lean_dec(v___x_2757_);
                    leanh::lean_inc(v___y_2759_);
                    v___y_2751_ = v___y_2759_;
                    v___y_2752_ = v___y_2759_;
                    state = 1;
                    continue;
                } else {
                    v___y_2751_ = v___y_2759_;
                    v___y_2752_ = v___x_2757_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v_x_2763_: *mut leanh::LeanObject,
    mut v_s_2764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2765_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2765_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_x_2763_, v_s_2764_);
    leanh::lean_dec(v_s_2764_);
    leanh::lean_dec_ref(v_x_2763_);
    return v_res_2765_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_s_2778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2779_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                if leanh::lean_obj_tag(v_s_2778_) == 0 {
                    v_size_2785_ = leanh::lean_ctor_get(v_s_2778_, 0);
                    leanh::lean_inc(v_size_2785_);
                    leanh::lean_dec_ref_known(v_s_2778_, 5);
                    v___y_2781_ = v_size_2785_;
                    state = 1;
                    continue;
                } else {
                    v___x_2786_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2781_ = v___x_2786_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2782_ = l_Nat_reprFast(v___y_2781_);
                v___x_2783_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2783_, 0, v___x_2782_);
                v___x_2784_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2784_, 0, v___x_2779_);
                leanh::lean_ctor_set(v___x_2784_, 1, v___x_2783_);
                return v___x_2784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(
    mut v_newState_2787_: *mut leanh::LeanObject,
    mut v_x_2788_: *mut leanh::LeanObject,
    mut v_x_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2789_) == 0 {
                    return v_x_2788_;
                } else {
                    v_head_2790_ = leanh::lean_ctor_get(v_x_2789_, 0);
                    leanh::lean_inc(v_head_2790_);
                    v_tail_2791_ = leanh::lean_ctor_get(v_x_2789_, 1);
                    leanh::lean_inc(v_tail_2791_);
                    leanh::lean_dec_ref_known(v_x_2789_, 2);
                    v___x_2792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_2787_, v_head_2790_);
                    if leanh::lean_obj_tag(v___x_2792_) == 1 {
                        v_val_2793_ = leanh::lean_ctor_get(v___x_2792_, 0);
                        leanh::lean_inc(v_val_2793_);
                        leanh::lean_dec_ref_known(v___x_2792_, 1);
                        v___x_2794_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_2790_, v_val_2793_, v_x_2788_);
                        v_x_2788_ = v___x_2794_;
                        v_x_2789_ = v_tail_2791_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2792_);
                        leanh::lean_dec(v_head_2790_);
                        v_x_2789_ = v_tail_2791_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2___boxed(
    mut v_newState_2797_: *mut leanh::LeanObject,
    mut v_x_2798_: *mut leanh::LeanObject,
    mut v_x_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_2797_, v_x_2798_, v_x_2799_);
    leanh::lean_dec(v_newState_2797_);
    return v_res_2800_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___oldState_2801_: *mut leanh::LeanObject,
    mut v_newState_2802_: *mut leanh::LeanObject,
    mut v_newItems_2803_: *mut leanh::LeanObject,
    mut v_otherState_2804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_2802_, v_otherState_2804_, v_newItems_2803_);
    return v___x_2805_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___oldState_2806_: *mut leanh::LeanObject,
    mut v_newState_2807_: *mut leanh::LeanObject,
    mut v_newItems_2808_: *mut leanh::LeanObject,
    mut v_otherState_2809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___oldState_2806_, v_newState_2807_, v_newItems_2808_, v_otherState_2809_);
    leanh::lean_dec(v_newState_2807_);
    leanh::lean_dec(v___oldState_2806_);
    return v_res_2810_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_m_2811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2812_ = leanh::lean_unsigned_to_nat(0);
                v___x_2813_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                v_r_2814_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_2813_, v_m_2811_);
                v___x_2815_ = lean_array_get_size(v_r_2814_);
                v___x_2816_ = lean_nat_dec_eq(v___x_2815_, v___x_2812_);
                if v___x_2816_ == 0 {
                    v___x_2817_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2818_ = lean_nat_sub(v___x_2815_, v___x_2817_);
                    v___x_2824_ = lean_nat_dec_le(v___x_2812_, v___x_2818_);
                    if v___x_2824_ == 0 {
                        leanh::lean_inc(v___x_2818_);
                        v___y_2820_ = v___x_2818_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2820_ = v___x_2812_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_r_2814_;
                }
            }
            1 => {
                v___x_2821_ = lean_nat_dec_le(v___y_2820_, v___x_2818_);
                if v___x_2821_ == 0 {
                    leanh::lean_dec(v___x_2818_);
                    leanh::lean_inc(v___y_2820_);
                    v___x_2822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2815_, v_r_2814_, v___y_2820_, v___y_2820_);
                    leanh::lean_dec(v___y_2820_);
                    return v___x_2822_;
                } else {
                    v___x_2823_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2815_, v_r_2814_, v___y_2820_, v___x_2818_);
                    leanh::lean_dec(v___x_2818_);
                    return v___x_2823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v_m_2825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2826_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_m_2825_);
    leanh::lean_dec(v_m_2825_);
    return v_res_2826_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___x_2827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2829_, 0, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___x_2830_: *mut leanh::LeanObject,
    mut v___y_2831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2832_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_2830_);
    return v_res_2832_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___x_2833_: *mut leanh::LeanObject,
    mut v_x_2834_: *mut leanh::LeanObject,
    mut v_x_2835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2837_, 0, v___x_2833_);
    return v___x_2837_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___x_2838_: *mut leanh::LeanObject,
    mut v_x_2839_: *mut leanh::LeanObject,
    mut v_x_2840_: *mut leanh::LeanObject,
    mut v___y_2841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2842_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_2838_, v_x_2839_, v_x_2840_);
    leanh::lean_dec_ref(v_x_2840_);
    leanh::lean_dec_ref(v_x_2839_);
    return v_res_2842_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
    v___x_2873_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v_a_2874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2875_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
    return v_res_2875_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(
    mut v_init_2876_: *mut leanh::LeanObject,
    mut v_t_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2876_, v_t_2877_);
    return v___x_2878_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_2879_: *mut leanh::LeanObject,
    mut v_t_2880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2881_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(v_init_2879_, v_t_2880_);
    leanh::lean_dec(v_t_2880_);
    return v_res_2881_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(
    mut v_n_2882_: *mut leanh::LeanObject,
    mut v_as_2883_: *mut leanh::LeanObject,
    mut v_lo_2884_: *mut leanh::LeanObject,
    mut v_hi_2885_: *mut leanh::LeanObject,
    mut v_w_2886_: *mut leanh::LeanObject,
    mut v_hlo_2887_: *mut leanh::LeanObject,
    mut v_hhi_2888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2882_, v_as_2883_, v_lo_2884_, v_hi_2885_);
    return v___x_2889_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(
    mut v_n_2890_: *mut leanh::LeanObject,
    mut v_as_2891_: *mut leanh::LeanObject,
    mut v_lo_2892_: *mut leanh::LeanObject,
    mut v_hi_2893_: *mut leanh::LeanObject,
    mut v_w_2894_: *mut leanh::LeanObject,
    mut v_hlo_2895_: *mut leanh::LeanObject,
    mut v_hhi_2896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(v_n_2890_, v_as_2891_, v_lo_2892_, v_hi_2893_, v_w_2894_, v_hlo_2895_, v_hhi_2896_);
    leanh::lean_dec(v_hi_2893_);
    leanh::lean_dec(v_n_2890_);
    return v_res_2897_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(
    mut v_n_2898_: *mut leanh::LeanObject,
    mut v_lo_2899_: *mut leanh::LeanObject,
    mut v_hi_2900_: *mut leanh::LeanObject,
    mut v_hhi_2901_: *mut leanh::LeanObject,
    mut v_pivot_2902_: *mut leanh::LeanObject,
    mut v_as_2903_: *mut leanh::LeanObject,
    mut v_i_2904_: *mut leanh::LeanObject,
    mut v_k_2905_: *mut leanh::LeanObject,
    mut v_ilo_2906_: *mut leanh::LeanObject,
    mut v_ik_2907_: *mut leanh::LeanObject,
    mut v_w_2908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2900_, v_pivot_2902_, v_as_2903_, v_i_2904_, v_k_2905_);
    return v___x_2909_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_n_2910_: *mut leanh::LeanObject,
    mut v_lo_2911_: *mut leanh::LeanObject,
    mut v_hi_2912_: *mut leanh::LeanObject,
    mut v_hhi_2913_: *mut leanh::LeanObject,
    mut v_pivot_2914_: *mut leanh::LeanObject,
    mut v_as_2915_: *mut leanh::LeanObject,
    mut v_i_2916_: *mut leanh::LeanObject,
    mut v_k_2917_: *mut leanh::LeanObject,
    mut v_ilo_2918_: *mut leanh::LeanObject,
    mut v_ik_2919_: *mut leanh::LeanObject,
    mut v_w_2920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(v_n_2910_, v_lo_2911_, v_hi_2912_, v_hhi_2913_, v_pivot_2914_, v_as_2915_, v_i_2916_, v_k_2917_, v_ilo_2918_, v_ik_2919_, v_w_2920_);
    leanh::lean_dec_ref(v_pivot_2914_);
    leanh::lean_dec(v_hi_2912_);
    leanh::lean_dec(v_lo_2911_);
    leanh::lean_dec(v_n_2910_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_2922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_2923_: u8 = 0;
    let mut v_map_u2081_2924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2923_ = leanh::lean_ctor_get_uint8(
                    v_m_2922_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2923_ == 0 {
                    return v_m_2922_;
                } else {
                    v_map_u2081_2924_ = leanh::lean_ctor_get(v_m_2922_, 0);
                    v_map_u2082_2925_ = leanh::lean_ctor_get(v_m_2922_, 1);
                    v_isSharedCheck_2933_ = (!leanh::lean_is_exclusive(v_m_2922_)) as u8;
                    if v_isSharedCheck_2933_ == 0 {
                        v___x_2927_ = v_m_2922_;
                        v_isShared_2928_ = v_isSharedCheck_2933_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_2925_);
                        leanh::lean_inc(v_map_u2081_2924_);
                        leanh::lean_dec(v_m_2922_);
                        v___x_2927_ = leanh::lean_box(0);
                        v_isShared_2928_ = v_isSharedCheck_2933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2929_ = 0;
                if v_isShared_2928_ == 0 {
                    v___x_2931_ = v___x_2927_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_map_u2081_2924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_map_u2082_2925_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_2931_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_2929_,
                );
                return v___x_2931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2934_: *mut leanh::LeanObject,
    mut v_m_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(v_m_2935_);
    return v___x_2936_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(
    mut v_x_2937_: *mut leanh::LeanObject,
    mut v_a_2938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2939_, 0, v_a_2938_);
    leanh::lean_inc_ref_n(v___x_2939_, 2);
    v___x_2940_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2940_, 0, v___x_2939_);
    leanh::lean_ctor_set(v___x_2940_, 1, v___x_2939_);
    leanh::lean_ctor_set(v___x_2940_, 2, v___x_2939_);
    return v___x_2940_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(
    mut v_x_2941_: *mut leanh::LeanObject,
    mut v_a_2942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2943_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(v_x_2941_, v_a_2942_);
    leanh::lean_dec_ref(v_x_2941_);
    return v_res_2943_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0()
-> u64 {
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u64 = 0;
    v___x_2944_ = leanh::lean_unsigned_to_nat(1723);
    v___x_2945_ = lean_uint64_of_nat(v___x_2944_);
    return v___x_2945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(
    mut v_x_2946_: *mut leanh::LeanObject,
    mut v_x_2947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: u64 = 0;
    let mut v___x_2957_: u64 = 0;
    let mut v___x_2958_: u64 = 0;
    let mut v_fold_2959_: u64 = 0;
    let mut v___x_2960_: u64 = 0;
    let mut v___x_2961_: u64 = 0;
    let mut v___x_2962_: u64 = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2964_: usize = 0;
    let mut v___x_2965_: usize = 0;
    let mut v___x_2966_: usize = 0;
    let mut v___x_2967_: usize = 0;
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u64 = 0;
    let mut v_hash_2975_: u64 = 0;
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2947_) == 0 {
                    return v_x_2946_;
                } else {
                    v_key_2948_ = leanh::lean_ctor_get(v_x_2947_, 0);
                    v_value_2949_ = leanh::lean_ctor_get(v_x_2947_, 1);
                    v_tail_2950_ = leanh::lean_ctor_get(v_x_2947_, 2);
                    v_isSharedCheck_2976_ = (!leanh::lean_is_exclusive(v_x_2947_)) as u8;
                    if v_isSharedCheck_2976_ == 0 {
                        v___x_2952_ = v_x_2947_;
                        v_isShared_2953_ = v_isSharedCheck_2976_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2950_);
                        leanh::lean_inc(v_value_2949_);
                        leanh::lean_inc(v_key_2948_);
                        leanh::lean_dec(v_x_2947_);
                        v___x_2952_ = leanh::lean_box(0);
                        v_isShared_2953_ = v_isSharedCheck_2976_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2954_ = lean_array_get_size(v_x_2946_);
                if leanh::lean_obj_tag(v_key_2948_) == 0 {
                    v___x_2974_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_2956_ = v___x_2974_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2975_ = leanh::lean_ctor_get_uint64(
                        v_key_2948_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2956_ = v_hash_2975_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2957_ = 32u64;
                v___x_2958_ = lean_uint64_shift_right(v___y_2956_, v___x_2957_);
                v_fold_2959_ = lean_uint64_xor(v___y_2956_, v___x_2958_);
                v___x_2960_ = 16u64;
                v___x_2961_ = lean_uint64_shift_right(v_fold_2959_, v___x_2960_);
                v___x_2962_ = lean_uint64_xor(v_fold_2959_, v___x_2961_);
                v___x_2963_ = lean_uint64_to_usize(v___x_2962_);
                v___x_2964_ = lean_usize_of_nat(v___x_2954_);
                v___x_2965_ = 1usize;
                v___x_2966_ = lean_usize_sub(v___x_2964_, v___x_2965_);
                v___x_2967_ = lean_usize_land(v___x_2963_, v___x_2966_);
                v___x_2968_ = lean_array_uget_borrowed(v_x_2946_, v___x_2967_);
                leanh::lean_inc(v___x_2968_);
                if v_isShared_2953_ == 0 {
                    leanh::lean_ctor_set(v___x_2952_, 2, v___x_2968_);
                    v___x_2970_ = v___x_2952_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_key_2948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_value_2949_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___x_2968_);
                    v___x_2970_ = v_reuseFailAlloc_2973_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2971_ = lean_array_uset(v_x_2946_, v___x_2967_, v___x_2970_);
                v_x_2946_ = v___x_2971_;
                v_x_2947_ = v_tail_2950_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(
    mut v_i_2977_: *mut leanh::LeanObject,
    mut v_source_2978_: *mut leanh::LeanObject,
    mut v_target_2979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v_es_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2980_ = lean_array_get_size(v_source_2978_);
                v___x_2981_ = lean_nat_dec_lt(v_i_2977_, v___x_2980_);
                if v___x_2981_ == 0 {
                    leanh::lean_dec_ref(v_source_2978_);
                    leanh::lean_dec(v_i_2977_);
                    return v_target_2979_;
                } else {
                    v_es_2982_ = lean_array_fget(v_source_2978_, v_i_2977_);
                    v___x_2983_ = leanh::lean_box(0);
                    v_source_2984_ = lean_array_fset(v_source_2978_, v_i_2977_, v___x_2983_);
                    v_target_2985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_target_2979_, v_es_2982_);
                    v___x_2986_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2987_ = lean_nat_add(v_i_2977_, v___x_2986_);
                    leanh::lean_dec(v_i_2977_);
                    v_i_2977_ = v___x_2987_;
                    v_source_2978_ = v_source_2984_;
                    v_target_2979_ = v_target_2985_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(
    mut v_data_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2990_ = lean_array_get_size(v_data_2989_);
    v___x_2991_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2992_ = lean_nat_mul(v___x_2990_, v___x_2991_);
    v___x_2993_ = leanh::lean_unsigned_to_nat(0);
    v___x_2994_ = leanh::lean_box(0);
    v___x_2995_ = lean_mk_array(v_nbuckets_2992_, v___x_2994_);
    v___x_2996_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v___x_2993_, v_data_2989_, v___x_2995_);
    return v___x_2996_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_x_2998_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2999_: u8 = 0;
    let mut v_key_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2998_) == 0 {
                    v___x_2999_ = 0;
                    return v___x_2999_;
                } else {
                    v_key_3000_ = leanh::lean_ctor_get(v_x_2998_, 0);
                    v_tail_3001_ = leanh::lean_ctor_get(v_x_2998_, 2);
                    v___x_3002_ = lean_name_eq(v_key_3000_, v_a_2997_);
                    if v___x_3002_ == 0 {
                        v_x_2998_ = v_tail_3001_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3002_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg___boxed(
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_x_3005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3006_: u8 = 0;
    let mut v_r_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_3004_, v_x_3005_);
    leanh::lean_dec(v_x_3005_);
    leanh::lean_dec(v_a_3004_);
    v_r_3007_ = leanh::lean_box((v_res_3006_) as usize);
    return v_r_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(
    mut v_a_3008_: *mut leanh::LeanObject,
    mut v_b_3009_: *mut leanh::LeanObject,
    mut v_x_3010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3010_) == 0 {
                    leanh::lean_dec(v_b_3009_);
                    leanh::lean_dec(v_a_3008_);
                    return v_x_3010_;
                } else {
                    v_key_3011_ = leanh::lean_ctor_get(v_x_3010_, 0);
                    v_value_3012_ = leanh::lean_ctor_get(v_x_3010_, 1);
                    v_tail_3013_ = leanh::lean_ctor_get(v_x_3010_, 2);
                    v_isSharedCheck_3025_ = (!leanh::lean_is_exclusive(v_x_3010_)) as u8;
                    if v_isSharedCheck_3025_ == 0 {
                        v___x_3015_ = v_x_3010_;
                        v_isShared_3016_ = v_isSharedCheck_3025_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_3013_);
                        leanh::lean_inc(v_value_3012_);
                        leanh::lean_inc(v_key_3011_);
                        leanh::lean_dec(v_x_3010_);
                        v___x_3015_ = leanh::lean_box(0);
                        v_isShared_3016_ = v_isSharedCheck_3025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3017_ = lean_name_eq(v_key_3011_, v_a_3008_);
                if v___x_3017_ == 0 {
                    v___x_3018_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_3008_, v_b_3009_, v_tail_3013_);
                    if v_isShared_3016_ == 0 {
                        leanh::lean_ctor_set(v___x_3015_, 2, v___x_3018_);
                        v___x_3020_ = v___x_3015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_key_3011_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_value_3012_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 2, v___x_3018_);
                        v___x_3020_ = v_reuseFailAlloc_3021_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_3012_);
                    leanh::lean_dec(v_key_3011_);
                    if v_isShared_3016_ == 0 {
                        leanh::lean_ctor_set(v___x_3015_, 1, v_b_3009_);
                        leanh::lean_ctor_set(v___x_3015_, 0, v_a_3008_);
                        v___x_3023_ = v___x_3015_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3024_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3008_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_b_3009_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_tail_3013_);
                        v___x_3023_ = v_reuseFailAlloc_3024_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3020_;
            }
            3 => {
                return v___x_3023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_m_3026_: *mut leanh::LeanObject,
    mut v_a_3027_: *mut leanh::LeanObject,
    mut v_b_3028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3036_: u64 = 0;
    let mut v___x_3037_: u64 = 0;
    let mut v___x_3038_: u64 = 0;
    let mut v_fold_3039_: u64 = 0;
    let mut v___x_3040_: u64 = 0;
    let mut v___x_3041_: u64 = 0;
    let mut v___x_3042_: u64 = 0;
    let mut v___x_3043_: usize = 0;
    let mut v___x_3044_: usize = 0;
    let mut v___x_3045_: usize = 0;
    let mut v___x_3046_: usize = 0;
    let mut v___x_3047_: usize = 0;
    let mut v_bkt_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v_val_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u64 = 0;
    let mut v_hash_3075_: u64 = 0;
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3029_ = leanh::lean_ctor_get(v_m_3026_, 0);
                v_buckets_3030_ = leanh::lean_ctor_get(v_m_3026_, 1);
                v_isSharedCheck_3076_ = (!leanh::lean_is_exclusive(v_m_3026_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v___x_3032_ = v_m_3026_;
                    v_isShared_3033_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_3030_);
                    leanh::lean_inc(v_size_3029_);
                    leanh::lean_dec(v_m_3026_);
                    v___x_3032_ = leanh::lean_box(0);
                    v_isShared_3033_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3034_ = lean_array_get_size(v_buckets_3030_);
                if leanh::lean_obj_tag(v_a_3027_) == 0 {
                    v___x_3074_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3036_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3075_ = leanh::lean_ctor_get_uint64(
                        v_a_3027_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3036_ = v_hash_3075_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3037_ = 32u64;
                v___x_3038_ = lean_uint64_shift_right(v___y_3036_, v___x_3037_);
                v_fold_3039_ = lean_uint64_xor(v___y_3036_, v___x_3038_);
                v___x_3040_ = 16u64;
                v___x_3041_ = lean_uint64_shift_right(v_fold_3039_, v___x_3040_);
                v___x_3042_ = lean_uint64_xor(v_fold_3039_, v___x_3041_);
                v___x_3043_ = lean_uint64_to_usize(v___x_3042_);
                v___x_3044_ = lean_usize_of_nat(v___x_3034_);
                v___x_3045_ = 1usize;
                v___x_3046_ = lean_usize_sub(v___x_3044_, v___x_3045_);
                v___x_3047_ = lean_usize_land(v___x_3043_, v___x_3046_);
                v_bkt_3048_ = lean_array_uget_borrowed(v_buckets_3030_, v___x_3047_);
                v___x_3049_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_3027_, v_bkt_3048_);
                if v___x_3049_ == 0 {
                    v___x_3050_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3051_ = lean_nat_add(v_size_3029_, v___x_3050_);
                    leanh::lean_dec(v_size_3029_);
                    leanh::lean_inc(v_bkt_3048_);
                    v___x_3052_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_3052_, 0, v_a_3027_);
                    leanh::lean_ctor_set(v___x_3052_, 1, v_b_3028_);
                    leanh::lean_ctor_set(v___x_3052_, 2, v_bkt_3048_);
                    v_buckets_x27_3053_ =
                        lean_array_uset(v_buckets_3030_, v___x_3047_, v___x_3052_);
                    v___x_3054_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3055_ = lean_nat_mul(v_size_x27_3051_, v___x_3054_);
                    v___x_3056_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3057_ = lean_nat_div(v___x_3055_, v___x_3056_);
                    leanh::lean_dec(v___x_3055_);
                    v___x_3058_ = lean_array_get_size(v_buckets_x27_3053_);
                    v___x_3059_ = lean_nat_dec_le(v___x_3057_, v___x_3058_);
                    leanh::lean_dec(v___x_3057_);
                    if v___x_3059_ == 0 {
                        v_val_3060_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_buckets_x27_3053_);
                        if v_isShared_3033_ == 0 {
                            leanh::lean_ctor_set(v___x_3032_, 1, v_val_3060_);
                            leanh::lean_ctor_set(v___x_3032_, 0, v_size_x27_3051_);
                            v___x_3062_ = v___x_3032_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3063_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3063_,
                                0,
                                v_size_x27_3051_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_val_3060_);
                            v___x_3062_ = v_reuseFailAlloc_3063_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3033_ == 0 {
                            leanh::lean_ctor_set(v___x_3032_, 1, v_buckets_x27_3053_);
                            leanh::lean_ctor_set(v___x_3032_, 0, v_size_x27_3051_);
                            v___x_3065_ = v___x_3032_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3066_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3066_,
                                0,
                                v_size_x27_3051_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_3066_,
                                1,
                                v_buckets_x27_3053_,
                            );
                            v___x_3065_ = v_reuseFailAlloc_3066_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_3048_);
                    v___x_3067_ = leanh::lean_box(0);
                    v_buckets_x27_3068_ =
                        lean_array_uset(v_buckets_3030_, v___x_3047_, v___x_3067_);
                    v___x_3069_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_3027_, v_b_3028_, v_bkt_3048_);
                    v___x_3070_ = lean_array_uset(v_buckets_x27_3068_, v___x_3047_, v___x_3069_);
                    if v_isShared_3033_ == 0 {
                        leanh::lean_ctor_set(v___x_3032_, 1, v___x_3070_);
                        v___x_3072_ = v___x_3032_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3073_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_size_3029_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3070_);
                        v___x_3072_ = v_reuseFailAlloc_3073_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3062_;
            }
            4 => {
                return v___x_3065_;
            }
            5 => {
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(
    mut v_x_3077_: *mut leanh::LeanObject,
    mut v_x_3078_: *mut leanh::LeanObject,
    mut v_x_3079_: *mut leanh::LeanObject,
    mut v_x_3080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3081_ = leanh::lean_ctor_get(v_x_3077_, 0);
                v_vs_3082_ = leanh::lean_ctor_get(v_x_3077_, 1);
                v_isSharedCheck_3106_ = (!leanh::lean_is_exclusive(v_x_3077_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3084_ = v_x_3077_;
                    v_isShared_3085_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_3082_);
                    leanh::lean_inc(v_ks_3081_);
                    leanh::lean_dec(v_x_3077_);
                    v___x_3084_ = leanh::lean_box(0);
                    v_isShared_3085_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3086_ = lean_array_get_size(v_ks_3081_);
                v___x_3087_ = lean_nat_dec_lt(v_x_3078_, v___x_3086_);
                if v___x_3087_ == 0 {
                    leanh::lean_dec(v_x_3078_);
                    v___x_3088_ = lean_array_push(v_ks_3081_, v_x_3079_);
                    v___x_3089_ = lean_array_push(v_vs_3082_, v_x_3080_);
                    if v_isShared_3085_ == 0 {
                        leanh::lean_ctor_set(v___x_3084_, 1, v___x_3089_);
                        leanh::lean_ctor_set(v___x_3084_, 0, v___x_3088_);
                        v___x_3091_ = v___x_3084_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3092_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3088_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
                        v___x_3091_ = v_reuseFailAlloc_3092_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_3093_ = lean_array_fget_borrowed(v_ks_3081_, v_x_3078_);
                    v___x_3094_ = lean_name_eq(v_x_3079_, v_k_x27_3093_);
                    if v___x_3094_ == 0 {
                        if v_isShared_3085_ == 0 {
                            v___x_3096_ = v___x_3084_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3100_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_ks_3081_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_vs_3082_);
                            v___x_3096_ = v_reuseFailAlloc_3100_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3101_ = lean_array_fset(v_ks_3081_, v_x_3078_, v_x_3079_);
                        v___x_3102_ = lean_array_fset(v_vs_3082_, v_x_3078_, v_x_3080_);
                        leanh::lean_dec(v_x_3078_);
                        if v_isShared_3085_ == 0 {
                            leanh::lean_ctor_set(v___x_3084_, 1, v___x_3102_);
                            leanh::lean_ctor_set(v___x_3084_, 0, v___x_3101_);
                            v___x_3104_ = v___x_3084_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3105_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3101_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3102_);
                            v___x_3104_ = v_reuseFailAlloc_3105_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3091_;
            }
            3 => {
                v___x_3097_ = leanh::lean_unsigned_to_nat(1);
                v___x_3098_ = lean_nat_add(v_x_3078_, v___x_3097_);
                leanh::lean_dec(v_x_3078_);
                v_x_3077_ = v___x_3096_;
                v_x_3078_ = v___x_3098_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_3104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_n_3107_: *mut leanh::LeanObject,
    mut v_k_3108_: *mut leanh::LeanObject,
    mut v_v_3109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3110_ = leanh::lean_unsigned_to_nat(0);
    v___x_3111_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_n_3107_, v___x_3110_, v_k_3108_, v_v_3109_);
    return v___x_3111_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_3112_: usize = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    v___x_3112_ = 5usize;
    v___x_3113_ = 1usize;
    v___x_3114_ = lean_usize_shift_left(v___x_3113_, v___x_3112_);
    return v___x_3114_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_3115_: usize = 0;
    let mut v___x_3116_: usize = 0;
    let mut v___x_3117_: usize = 0;
    v___x_3115_ = 1usize;
    v___x_3116_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_3117_ = lean_usize_sub(v___x_3116_, v___x_3115_);
    return v___x_3117_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3118_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(
    mut v_x_3119_: *mut leanh::LeanObject,
    mut v_x_3120_: usize,
    mut v_x_3121_: usize,
    mut v_x_3122_: *mut leanh::LeanObject,
    mut v_x_3123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: usize = 0;
    let mut v_j_3129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v_v_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v_node_3156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3166_: u8 = 0;
    let mut v___x_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_unused_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: u8 = 0;
    let mut v_ks_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v_reuseFailAlloc_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3119_) == 0 {
                    v_es_3124_ = leanh::lean_ctor_get(v_x_3119_, 0);
                    v___x_3125_ = 5usize;
                    v___x_3126_ = 1usize;
                    v___x_3127_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_3128_ = lean_usize_land(v_x_3120_, v___x_3127_);
                    v_j_3129_ = lean_usize_to_nat(v___x_3128_);
                    v___x_3130_ = lean_array_get_size(v_es_3124_);
                    v___x_3131_ = lean_nat_dec_lt(v_j_3129_, v___x_3130_);
                    if v___x_3131_ == 0 {
                        leanh::lean_dec(v_j_3129_);
                        leanh::lean_dec(v_x_3123_);
                        leanh::lean_dec(v_x_3122_);
                        return v_x_3119_;
                    } else {
                        leanh::lean_inc_ref(v_es_3124_);
                        v_isSharedCheck_3168_ = (!leanh::lean_is_exclusive(v_x_3119_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v_unused_3169_ = leanh::lean_ctor_get(v_x_3119_, 0);
                            leanh::lean_dec(v_unused_3169_);
                            v___x_3133_ = v_x_3119_;
                            v_isShared_3134_ = v_isSharedCheck_3168_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_3119_);
                            v___x_3133_ = leanh::lean_box(0);
                            v_isShared_3134_ = v_isSharedCheck_3168_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3170_ = leanh::lean_ctor_get(v_x_3119_, 0);
                    v_vs_3171_ = leanh::lean_ctor_get(v_x_3119_, 1);
                    v_isSharedCheck_3191_ = (!leanh::lean_is_exclusive(v_x_3119_)) as u8;
                    if v_isSharedCheck_3191_ == 0 {
                        v___x_3173_ = v_x_3119_;
                        v_isShared_3174_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_3171_);
                        leanh::lean_inc(v_ks_3170_);
                        leanh::lean_dec(v_x_3119_);
                        v___x_3173_ = leanh::lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3135_ = lean_array_fget(v_es_3124_, v_j_3129_);
                v___x_3136_ = leanh::lean_box(0);
                v_xs_x27_3137_ = lean_array_fset(v_es_3124_, v_j_3129_, v___x_3136_);
                match leanh::lean_obj_tag(v_v_3135_) {
                    0 => {
                        v_key_3144_ = leanh::lean_ctor_get(v_v_3135_, 0);
                        v_val_3145_ = leanh::lean_ctor_get(v_v_3135_, 1);
                        v_isSharedCheck_3155_ = (!leanh::lean_is_exclusive(v_v_3135_)) as u8;
                        if v_isSharedCheck_3155_ == 0 {
                            v___x_3147_ = v_v_3135_;
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3145_);
                            leanh::lean_inc(v_key_3144_);
                            leanh::lean_dec(v_v_3135_);
                            v___x_3147_ = leanh::lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3156_ = leanh::lean_ctor_get(v_v_3135_, 0);
                        v_isSharedCheck_3166_ = (!leanh::lean_is_exclusive(v_v_3135_)) as u8;
                        if v_isSharedCheck_3166_ == 0 {
                            v___x_3158_ = v_v_3135_;
                            v_isShared_3159_ = v_isSharedCheck_3166_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_3156_);
                            leanh::lean_dec(v_v_3135_);
                            v___x_3158_ = leanh::lean_box(0);
                            v_isShared_3159_ = v_isSharedCheck_3166_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3167_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3167_, 0, v_x_3122_);
                        leanh::lean_ctor_set(v___x_3167_, 1, v_x_3123_);
                        v___y_3139_ = v___x_3167_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3140_ = lean_array_fset(v_xs_x27_3137_, v_j_3129_, v___y_3139_);
                leanh::lean_dec(v_j_3129_);
                if v_isShared_3134_ == 0 {
                    leanh::lean_ctor_set(v___x_3133_, 0, v___x_3140_);
                    v___x_3142_ = v___x_3133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3142_;
            }
            4 => {
                v___x_3149_ = lean_name_eq(v_x_3122_, v_key_3144_);
                if v___x_3149_ == 0 {
                    leanh::lean_del_object(v___x_3147_);
                    v___x_3150_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3144_,
                        v_val_3145_,
                        v_x_3122_,
                        v_x_3123_,
                    );
                    v___x_3151_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3151_, 0, v___x_3150_);
                    v___y_3139_ = v___x_3151_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_3145_);
                    leanh::lean_dec(v_key_3144_);
                    if v_isShared_3148_ == 0 {
                        leanh::lean_ctor_set(v___x_3147_, 1, v_x_3123_);
                        leanh::lean_ctor_set(v___x_3147_, 0, v_x_3122_);
                        v___x_3153_ = v___x_3147_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_x_3122_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_x_3123_);
                        v___x_3153_ = v_reuseFailAlloc_3154_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_3139_ = v___x_3153_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3160_ = lean_usize_shift_right(v_x_3120_, v___x_3125_);
                v___x_3161_ = lean_usize_add(v_x_3121_, v___x_3126_);
                v___x_3162_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_node_3156_, v___x_3160_, v___x_3161_, v_x_3122_, v_x_3123_);
                if v_isShared_3159_ == 0 {
                    leanh::lean_ctor_set(v___x_3158_, 0, v___x_3162_);
                    v___x_3164_ = v___x_3158_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
                    v___x_3164_ = v_reuseFailAlloc_3165_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_3139_ = v___x_3164_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_3174_ == 0 {
                    v___x_3176_ = v___x_3173_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_ks_3170_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_vs_3171_);
                    v___x_3176_ = v_reuseFailAlloc_3190_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_3177_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v___x_3176_, v_x_3122_, v_x_3123_);
                v___x_3185_ = 7usize;
                v___x_3186_ = lean_usize_dec_le(v___x_3185_, v_x_3121_);
                if v___x_3186_ == 0 {
                    v___x_3187_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_3177_);
                    v___x_3188_ = leanh::lean_unsigned_to_nat(4);
                    v___x_3189_ = lean_nat_dec_lt(v___x_3187_, v___x_3188_);
                    leanh::lean_dec(v___x_3187_);
                    v___y_3179_ = v___x_3189_;
                    state = 10;
                    continue;
                } else {
                    v___y_3179_ = v___x_3186_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3179_ == 0 {
                    v_ks_3180_ = leanh::lean_ctor_get(v_newNode_3177_, 0);
                    leanh::lean_inc_ref(v_ks_3180_);
                    v_vs_3181_ = leanh::lean_ctor_get(v_newNode_3177_, 1);
                    leanh::lean_inc_ref(v_vs_3181_);
                    leanh::lean_dec_ref(v_newNode_3177_);
                    v___x_3182_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2);
                    v___x_3184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_3121_, v_ks_3180_, v_vs_3181_, v___x_3182_, v___x_3183_);
                    leanh::lean_dec_ref(v_vs_3181_);
                    leanh::lean_dec_ref(v_ks_3180_);
                    return v___x_3184_;
                } else {
                    return v_newNode_3177_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_depth_3192_: usize,
    mut v_keys_3193_: *mut leanh::LeanObject,
    mut v_vals_3194_: *mut leanh::LeanObject,
    mut v_i_3195_: *mut leanh::LeanObject,
    mut v_entries_3196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v_k_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: u64 = 0;
    let mut v_h_3203_: usize = 0;
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: usize = 0;
    let mut v___x_3207_: usize = 0;
    let mut v___x_3208_: usize = 0;
    let mut v_h_3209_: usize = 0;
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u64 = 0;
    let mut v_hash_3214_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3197_ = lean_array_get_size(v_keys_3193_);
                v___x_3198_ = lean_nat_dec_lt(v_i_3195_, v___x_3197_);
                if v___x_3198_ == 0 {
                    leanh::lean_dec(v_i_3195_);
                    return v_entries_3196_;
                } else {
                    v_k_3199_ = lean_array_fget_borrowed(v_keys_3193_, v_i_3195_);
                    v_v_3200_ = lean_array_fget_borrowed(v_vals_3194_, v_i_3195_);
                    if leanh::lean_obj_tag(v_k_3199_) == 0 {
                        v___x_3213_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                        v___y_3202_ = v___x_3213_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3214_ = leanh::lean_ctor_get_uint64(
                            v_k_3199_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_3202_ = v_hash_3214_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_3203_ = lean_uint64_to_usize(v___y_3202_);
                v___x_3204_ = 5usize;
                v___x_3205_ = leanh::lean_unsigned_to_nat(1);
                v___x_3206_ = 1usize;
                v___x_3207_ = lean_usize_sub(v_depth_3192_, v___x_3206_);
                v___x_3208_ = lean_usize_mul(v___x_3204_, v___x_3207_);
                v_h_3209_ = lean_usize_shift_right(v_h_3203_, v___x_3208_);
                v___x_3210_ = lean_nat_add(v_i_3195_, v___x_3205_);
                leanh::lean_dec(v_i_3195_);
                leanh::lean_inc(v_v_3200_);
                leanh::lean_inc(v_k_3199_);
                v___x_3211_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_entries_3196_, v_h_3209_, v_depth_3192_, v_k_3199_, v_v_3200_);
                v_i_3195_ = v___x_3210_;
                v_entries_3196_ = v___x_3211_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_depth_3215_: *mut leanh::LeanObject,
    mut v_keys_3216_: *mut leanh::LeanObject,
    mut v_vals_3217_: *mut leanh::LeanObject,
    mut v_i_3218_: *mut leanh::LeanObject,
    mut v_entries_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3220_: usize = 0;
    let mut v_res_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3220_ = leanh::lean_unbox_usize(v_depth_3215_);
    leanh::lean_dec(v_depth_3215_);
    v_res_3221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_3220_, v_keys_3216_, v_vals_3217_, v_i_3218_, v_entries_3219_);
    leanh::lean_dec_ref(v_vals_3217_);
    leanh::lean_dec_ref(v_keys_3216_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_3222_: *mut leanh::LeanObject,
    mut v_x_3223_: *mut leanh::LeanObject,
    mut v_x_3224_: *mut leanh::LeanObject,
    mut v_x_3225_: *mut leanh::LeanObject,
    mut v_x_3226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1110__boxed_3227_: usize = 0;
    let mut v_x_1111__boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1110__boxed_3227_ = leanh::lean_unbox_usize(v_x_3223_);
    leanh::lean_dec(v_x_3223_);
    v_x_1111__boxed_3228_ = leanh::lean_unbox_usize(v_x_3224_);
    leanh::lean_dec(v_x_3224_);
    v_res_3229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3222_, v_x_1110__boxed_3227_, v_x_1111__boxed_3228_, v_x_3225_, v_x_3226_);
    return v_res_3229_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(
    mut v_x_3230_: *mut leanh::LeanObject,
    mut v_x_3231_: *mut leanh::LeanObject,
    mut v_x_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3234_: u64 = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u64 = 0;
    let mut v_hash_3239_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3231_) == 0 {
                    v___x_3238_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3234_ = v___x_3238_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3239_ = leanh::lean_ctor_get_uint64(
                        v_x_3231_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3234_ = v_hash_3239_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3235_ = lean_uint64_to_usize(v___y_3234_);
                v___x_3236_ = 1usize;
                v___x_3237_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3230_, v___x_3235_, v___x_3236_, v_x_3231_, v_x_3232_);
                return v___x_3237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_3240_: *mut leanh::LeanObject,
    mut v_x_3241_: *mut leanh::LeanObject,
    mut v_x_3242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_3243_: u8 = 0;
    let mut v_map_u2081_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_map_u2081_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_3243_ = leanh::lean_ctor_get_uint8(
                    v_x_3240_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_3243_ == 0 {
                    v_map_u2081_3244_ = leanh::lean_ctor_get(v_x_3240_, 0);
                    v_map_u2082_3245_ = leanh::lean_ctor_get(v_x_3240_, 1);
                    v_isSharedCheck_3253_ = (!leanh::lean_is_exclusive(v_x_3240_)) as u8;
                    if v_isSharedCheck_3253_ == 0 {
                        v___x_3247_ = v_x_3240_;
                        v_isShared_3248_ = v_isSharedCheck_3253_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_3245_);
                        leanh::lean_inc(v_map_u2081_3244_);
                        leanh::lean_dec(v_x_3240_);
                        v___x_3247_ = leanh::lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3253_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_3254_ = leanh::lean_ctor_get(v_x_3240_, 0);
                    v_map_u2082_3255_ = leanh::lean_ctor_get(v_x_3240_, 1);
                    v_isSharedCheck_3263_ = (!leanh::lean_is_exclusive(v_x_3240_)) as u8;
                    if v_isSharedCheck_3263_ == 0 {
                        v___x_3257_ = v_x_3240_;
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_map_u2082_3255_);
                        leanh::lean_inc(v_map_u2081_3254_);
                        leanh::lean_dec(v_x_3240_);
                        v___x_3257_ = leanh::lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3249_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_map_u2082_3245_, v_x_3241_, v_x_3242_);
                if v_isShared_3248_ == 0 {
                    leanh::lean_ctor_set(v___x_3247_, 1, v___x_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_map_u2081_3244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3252_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_3243_,
                    );
                    v___x_3251_ = v_reuseFailAlloc_3252_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3251_;
            }
            3 => {
                v___x_3259_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_map_u2081_3254_, v_x_3241_, v_x_3242_);
                if v_isShared_3258_ == 0 {
                    leanh::lean_ctor_set(v___x_3257_, 0, v___x_3259_);
                    v___x_3261_ = v___x_3257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_map_u2082_3255_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3262_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        v_stage_u2081_3243_,
                    );
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(
    mut v_d_3264_: *mut leanh::LeanObject,
    mut v_x_3265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_3266_ = leanh::lean_ctor_get(v_x_3265_, 0);
    leanh::lean_inc(v_fst_3266_);
    v_snd_3267_ = leanh::lean_ctor_get(v_x_3265_, 1);
    leanh::lean_inc(v_snd_3267_);
    leanh::lean_dec_ref(v_x_3265_);
    v___x_3268_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_d_3264_, v_fst_3266_, v_snd_3267_);
    return v___x_3268_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3275_ = leanh::lean_box(0);
    v___x_3276_ = leanh::lean_unsigned_to_nat(16);
    v___x_3277_ = lean_mk_array(v___x_3276_, v___x_3275_);
    return v___x_3277_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3279_ = leanh::lean_unsigned_to_nat(0);
    v___x_3280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3280_, 0, v___x_3279_);
    leanh::lean_ctor_set(v___x_3280_, 1, v___x_3278_);
    return v___x_3280_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3281_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3283_, 0, v___x_3282_);
    return v___x_3283_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3285_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3286_ = 1;
    v___x_3287_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
    leanh::lean_ctor_set(v___x_3287_, 0, v___x_3285_);
    leanh::lean_ctor_set(v___x_3287_, 1, v___x_3284_);
    leanh::lean_ctor_set_uint8(
        v___x_3287_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
        v___x_3286_,
    );
    return v___x_3287_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3288_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___f_3289_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___f_3291_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3292_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3293_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3293_, 0, v___x_3292_);
    leanh::lean_ctor_set(v___x_3293_, 1, v___f_3291_);
    leanh::lean_ctor_set(v___x_3293_, 2, v___x_3290_);
    leanh::lean_ctor_set(v___x_3293_, 3, v___f_3289_);
    leanh::lean_ctor_set(v___x_3293_, 4, v___f_3288_);
    return v___x_3293_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3296_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3295_);
    return v___x_3296_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(
    mut v_a_3297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3298_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
    return v_res_3298_;
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_3299_: *mut leanh::LeanObject,
    mut v_x_3300_: *mut leanh::LeanObject,
    mut v_x_3301_: *mut leanh::LeanObject,
    mut v_x_3302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3303_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_x_3300_, v_x_3301_, v_x_3302_);
    return v___x_3303_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(
    mut v_00_u03b2_3304_: *mut leanh::LeanObject,
    mut v_x_3305_: *mut leanh::LeanObject,
    mut v_x_3306_: *mut leanh::LeanObject,
    mut v_x_3307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_3305_, v_x_3306_, v_x_3307_);
    return v___x_3308_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_3309_: *mut leanh::LeanObject,
    mut v_m_3310_: *mut leanh::LeanObject,
    mut v_a_3311_: *mut leanh::LeanObject,
    mut v_b_3312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_3310_, v_a_3311_, v_b_3312_);
    return v___x_3313_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_00_u03b2_3314_: *mut leanh::LeanObject,
    mut v_x_3315_: *mut leanh::LeanObject,
    mut v_x_3316_: usize,
    mut v_x_3317_: usize,
    mut v_x_3318_: *mut leanh::LeanObject,
    mut v_x_3319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3315_, v_x_3316_, v_x_3317_, v_x_3318_, v_x_3319_);
    return v___x_3320_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3321_: *mut leanh::LeanObject,
    mut v_x_3322_: *mut leanh::LeanObject,
    mut v_x_3323_: *mut leanh::LeanObject,
    mut v_x_3324_: *mut leanh::LeanObject,
    mut v_x_3325_: *mut leanh::LeanObject,
    mut v_x_3326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1451__boxed_3327_: usize = 0;
    let mut v_x_1452__boxed_3328_: usize = 0;
    let mut v_res_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1451__boxed_3327_ = leanh::lean_unbox_usize(v_x_3323_);
    leanh::lean_dec(v_x_3323_);
    v_x_1452__boxed_3328_ = leanh::lean_unbox_usize(v_x_3324_);
    leanh::lean_dec(v_x_3324_);
    v_res_3329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_3321_, v_x_3322_, v_x_1451__boxed_3327_, v_x_1452__boxed_3328_, v_x_3325_, v_x_3326_);
    return v_res_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(
    mut v_00_u03b2_3330_: *mut leanh::LeanObject,
    mut v_a_3331_: *mut leanh::LeanObject,
    mut v_x_3332_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3333_: u8 = 0;
    v___x_3333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_3331_, v_x_3332_);
    return v___x_3333_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3334_: *mut leanh::LeanObject,
    mut v_a_3335_: *mut leanh::LeanObject,
    mut v_x_3336_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3337_: u8 = 0;
    let mut v_r_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_3334_, v_a_3335_, v_x_3336_);
    leanh::lean_dec(v_x_3336_);
    leanh::lean_dec(v_a_3335_);
    v_r_3338_ = leanh::lean_box((v_res_3337_) as usize);
    return v_r_3338_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5(
    mut v_00_u03b2_3339_: *mut leanh::LeanObject,
    mut v_data_3340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_data_3340_);
    return v___x_3341_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6(
    mut v_00_u03b2_3342_: *mut leanh::LeanObject,
    mut v_a_3343_: *mut leanh::LeanObject,
    mut v_b_3344_: *mut leanh::LeanObject,
    mut v_x_3345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_3343_, v_b_3344_, v_x_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3347_: *mut leanh::LeanObject,
    mut v_n_3348_: *mut leanh::LeanObject,
    mut v_k_3349_: *mut leanh::LeanObject,
    mut v_v_3350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v_n_3348_, v_k_3349_, v_v_3350_);
    return v___x_3351_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3352_: *mut leanh::LeanObject,
    mut v_depth_3353_: usize,
    mut v_keys_3354_: *mut leanh::LeanObject,
    mut v_vals_3355_: *mut leanh::LeanObject,
    mut v_heq_3356_: *mut leanh::LeanObject,
    mut v_i_3357_: *mut leanh::LeanObject,
    mut v_entries_3358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_3353_, v_keys_3354_, v_vals_3355_, v_i_3357_, v_entries_3358_);
    return v___x_3359_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3360_: *mut leanh::LeanObject,
    mut v_depth_3361_: *mut leanh::LeanObject,
    mut v_keys_3362_: *mut leanh::LeanObject,
    mut v_vals_3363_: *mut leanh::LeanObject,
    mut v_heq_3364_: *mut leanh::LeanObject,
    mut v_i_3365_: *mut leanh::LeanObject,
    mut v_entries_3366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_3367_: usize = 0;
    let mut v_res_3368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3367_ = leanh::lean_unbox_usize(v_depth_3361_);
    leanh::lean_dec(v_depth_3361_);
    v_res_3368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3360_, v_depth_boxed_3367_, v_keys_3362_, v_vals_3363_, v_heq_3364_, v_i_3365_, v_entries_3366_);
    leanh::lean_dec_ref(v_vals_3363_);
    leanh::lean_dec_ref(v_keys_3362_);
    return v_res_3368_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b2_3369_: *mut leanh::LeanObject,
    mut v_i_3370_: *mut leanh::LeanObject,
    mut v_source_3371_: *mut leanh::LeanObject,
    mut v_target_3372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3373_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_i_3370_, v_source_3371_, v_target_3372_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3374_: *mut leanh::LeanObject,
    mut v_x_3375_: *mut leanh::LeanObject,
    mut v_x_3376_: *mut leanh::LeanObject,
    mut v_x_3377_: *mut leanh::LeanObject,
    mut v_x_3378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3375_, v_x_3376_, v_x_3377_, v_x_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(
    mut v_00_u03b2_3380_: *mut leanh::LeanObject,
    mut v_x_3381_: *mut leanh::LeanObject,
    mut v_x_3382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_x_3381_, v_x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
    mut v_as_3384_: *mut leanh::LeanObject,
    mut v_k_3385_: *mut leanh::LeanObject,
    mut v_x_3386_: *mut leanh::LeanObject,
    mut v_x_3387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3388_ = lean_nat_add(v_x_3386_, v_x_3387_);
                v___x_3389_ = leanh::lean_unsigned_to_nat(1);
                v_m_3390_ = lean_nat_shiftr(v___x_3388_, v___x_3389_);
                leanh::lean_dec(v___x_3388_);
                v_a_3391_ = lean_array_fget_borrowed(v_as_3384_, v_m_3390_);
                v___x_3392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3391_, v_k_3385_);
                if v___x_3392_ == 0 {
                    leanh::lean_dec(v_x_3387_);
                    v___x_3393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3385_, v_a_3391_);
                    if v___x_3393_ == 0 {
                        leanh::lean_dec(v_m_3390_);
                        leanh::lean_dec(v_x_3386_);
                        leanh::lean_inc(v_a_3391_);
                        v___x_3394_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3394_, 0, v_a_3391_);
                        return v___x_3394_;
                    } else {
                        v___x_3395_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3396_ = lean_nat_dec_eq(v_m_3390_, v___x_3395_);
                        if v___x_3396_ == 0 {
                            v___x_3397_ = lean_nat_sub(v_m_3390_, v___x_3389_);
                            leanh::lean_dec(v_m_3390_);
                            v___x_3398_ = lean_nat_dec_lt(v___x_3397_, v_x_3386_);
                            if v___x_3398_ == 0 {
                                v_x_3387_ = v___x_3397_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_3397_);
                                leanh::lean_dec(v_x_3386_);
                                v___x_3400_ = leanh::lean_box(0);
                                return v___x_3400_;
                            }
                        } else {
                            leanh::lean_dec(v_m_3390_);
                            leanh::lean_dec(v_x_3386_);
                            v___x_3401_ = leanh::lean_box(0);
                            return v___x_3401_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_3386_);
                    v___x_3402_ = lean_nat_add(v_m_3390_, v___x_3389_);
                    leanh::lean_dec(v_m_3390_);
                    v___x_3403_ = lean_nat_dec_le(v___x_3402_, v_x_3387_);
                    if v___x_3403_ == 0 {
                        leanh::lean_dec(v___x_3402_);
                        leanh::lean_dec(v_x_3387_);
                        v___x_3404_ = leanh::lean_box(0);
                        return v___x_3404_;
                    } else {
                        v_x_3386_ = v___x_3402_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg___boxed(
    mut v_as_3406_: *mut leanh::LeanObject,
    mut v_k_3407_: *mut leanh::LeanObject,
    mut v_x_3408_: *mut leanh::LeanObject,
    mut v_x_3409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3410_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
        v_as_3406_, v_k_3407_, v_x_3408_, v_x_3409_,
    );
    leanh::lean_dec_ref(v_k_3407_);
    leanh::lean_dec_ref(v_as_3406_);
    return v_res_3410_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_3411_: *mut leanh::LeanObject,
    mut v_vals_3412_: *mut leanh::LeanObject,
    mut v_i_3413_: *mut leanh::LeanObject,
    mut v_k_3414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3415_ = lean_array_get_size(v_keys_3411_);
                v___x_3416_ = lean_nat_dec_lt(v_i_3413_, v___x_3415_);
                if v___x_3416_ == 0 {
                    leanh::lean_dec(v_i_3413_);
                    v___x_3417_ = leanh::lean_box(0);
                    return v___x_3417_;
                } else {
                    v_k_x27_3418_ = lean_array_fget_borrowed(v_keys_3411_, v_i_3413_);
                    v___x_3419_ = lean_name_eq(v_k_3414_, v_k_x27_3418_);
                    if v___x_3419_ == 0 {
                        v___x_3420_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3421_ = lean_nat_add(v_i_3413_, v___x_3420_);
                        leanh::lean_dec(v_i_3413_);
                        v_i_3413_ = v___x_3421_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3423_ = lean_array_fget_borrowed(v_vals_3412_, v_i_3413_);
                        leanh::lean_dec(v_i_3413_);
                        leanh::lean_inc(v___x_3423_);
                        v___x_3424_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3424_, 0, v___x_3423_);
                        return v___x_3424_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_3425_: *mut leanh::LeanObject,
    mut v_vals_3426_: *mut leanh::LeanObject,
    mut v_i_3427_: *mut leanh::LeanObject,
    mut v_k_3428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3425_, v_vals_3426_, v_i_3427_, v_k_3428_);
    leanh::lean_dec(v_k_3428_);
    leanh::lean_dec_ref(v_vals_3426_);
    leanh::lean_dec_ref(v_keys_3425_);
    return v_res_3429_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(
    mut v_x_3430_: *mut leanh::LeanObject,
    mut v_x_3431_: usize,
    mut v_x_3432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: usize = 0;
    let mut v_j_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_3449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_3450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3430_) == 0 {
                    v_es_3433_ = leanh::lean_ctor_get(v_x_3430_, 0);
                    v___x_3434_ = leanh::lean_box(2);
                    v___x_3435_ = 5usize;
                    v___x_3436_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_3437_ = lean_usize_land(v_x_3431_, v___x_3436_);
                    v_j_3438_ = lean_usize_to_nat(v___x_3437_);
                    v___x_3439_ = lean_array_get_borrowed(v___x_3434_, v_es_3433_, v_j_3438_);
                    leanh::lean_dec(v_j_3438_);
                    match leanh::lean_obj_tag(v___x_3439_) {
                        0 => {
                            v_key_3440_ = leanh::lean_ctor_get(v___x_3439_, 0);
                            v_val_3441_ = leanh::lean_ctor_get(v___x_3439_, 1);
                            v___x_3442_ = lean_name_eq(v_x_3432_, v_key_3440_);
                            if v___x_3442_ == 0 {
                                v___x_3443_ = leanh::lean_box(0);
                                return v___x_3443_;
                            } else {
                                leanh::lean_inc(v_val_3441_);
                                v___x_3444_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3444_, 0, v_val_3441_);
                                return v___x_3444_;
                            }
                        }
                        1 => {
                            v_node_3445_ = leanh::lean_ctor_get(v___x_3439_, 0);
                            v___x_3446_ = lean_usize_shift_right(v_x_3431_, v___x_3435_);
                            v_x_3430_ = v_node_3445_;
                            v_x_3431_ = v___x_3446_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3448_ = leanh::lean_box(0);
                            return v___x_3448_;
                        }
                    }
                } else {
                    v_ks_3449_ = leanh::lean_ctor_get(v_x_3430_, 0);
                    v_vs_3450_ = leanh::lean_ctor_get(v_x_3430_, 1);
                    v___x_3451_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3452_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_3449_, v_vs_3450_, v___x_3451_, v_x_3432_);
                    return v___x_3452_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3453_: *mut leanh::LeanObject,
    mut v_x_3454_: *mut leanh::LeanObject,
    mut v_x_3455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_615__boxed_3456_: usize = 0;
    let mut v_res_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_615__boxed_3456_ = leanh::lean_unbox_usize(v_x_3454_);
    leanh::lean_dec(v_x_3454_);
    v_res_3457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_3453_, v_x_615__boxed_3456_, v_x_3455_);
    leanh::lean_dec(v_x_3455_);
    leanh::lean_dec_ref(v_x_3453_);
    return v_res_3457_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(
    mut v_x_3458_: *mut leanh::LeanObject,
    mut v_x_3459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3461_: u64 = 0;
    let mut v___x_3462_: usize = 0;
    let mut v___x_3463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u64 = 0;
    let mut v_hash_3465_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3459_) == 0 {
                    v___x_3464_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3461_ = v___x_3464_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3465_ = leanh::lean_ctor_get_uint64(
                        v_x_3459_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3461_ = v_hash_3465_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3462_ = lean_uint64_to_usize(v___y_3461_);
                v___x_3463_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_3458_, v___x_3462_, v_x_3459_);
                return v___x_3463_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg___boxed(
    mut v_x_3466_: *mut leanh::LeanObject,
    mut v_x_3467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_3466_, v_x_3467_);
    leanh::lean_dec(v_x_3467_);
    leanh::lean_dec_ref(v_x_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(
    mut v_a_3469_: *mut leanh::LeanObject,
    mut v_x_3470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3470_) == 0 {
                    v___x_3471_ = leanh::lean_box(0);
                    return v___x_3471_;
                } else {
                    v_key_3472_ = leanh::lean_ctor_get(v_x_3470_, 0);
                    v_value_3473_ = leanh::lean_ctor_get(v_x_3470_, 1);
                    v_tail_3474_ = leanh::lean_ctor_get(v_x_3470_, 2);
                    v___x_3475_ = lean_name_eq(v_key_3472_, v_a_3469_);
                    if v___x_3475_ == 0 {
                        v_x_3470_ = v_tail_3474_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_3473_);
                        v___x_3477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3477_, 0, v_value_3473_);
                        return v___x_3477_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_x_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_3478_, v_x_3479_);
    leanh::lean_dec(v_x_3479_);
    leanh::lean_dec(v_a_3478_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(
    mut v_m_3481_: *mut leanh::LeanObject,
    mut v_a_3482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_3483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: u64 = 0;
    let mut v___x_3487_: u64 = 0;
    let mut v___x_3488_: u64 = 0;
    let mut v_fold_3489_: u64 = 0;
    let mut v___x_3490_: u64 = 0;
    let mut v___x_3491_: u64 = 0;
    let mut v___x_3492_: u64 = 0;
    let mut v___x_3493_: usize = 0;
    let mut v___x_3494_: usize = 0;
    let mut v___x_3495_: usize = 0;
    let mut v___x_3496_: usize = 0;
    let mut v___x_3497_: usize = 0;
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: u64 = 0;
    let mut v_hash_3501_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3483_ = leanh::lean_ctor_get(v_m_3481_, 1);
                v___x_3484_ = lean_array_get_size(v_buckets_3483_);
                if leanh::lean_obj_tag(v_a_3482_) == 0 {
                    v___x_3500_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3486_ = v___x_3500_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3501_ = leanh::lean_ctor_get_uint64(
                        v_a_3482_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_3486_ = v_hash_3501_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3487_ = 32u64;
                v___x_3488_ = lean_uint64_shift_right(v___y_3486_, v___x_3487_);
                v_fold_3489_ = lean_uint64_xor(v___y_3486_, v___x_3488_);
                v___x_3490_ = 16u64;
                v___x_3491_ = lean_uint64_shift_right(v_fold_3489_, v___x_3490_);
                v___x_3492_ = lean_uint64_xor(v_fold_3489_, v___x_3491_);
                v___x_3493_ = lean_uint64_to_usize(v___x_3492_);
                v___x_3494_ = lean_usize_of_nat(v___x_3484_);
                v___x_3495_ = 1usize;
                v___x_3496_ = lean_usize_sub(v___x_3494_, v___x_3495_);
                v___x_3497_ = lean_usize_land(v___x_3493_, v___x_3496_);
                v___x_3498_ = lean_array_uget_borrowed(v_buckets_3483_, v___x_3497_);
                v___x_3499_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_3482_, v___x_3498_);
                return v___x_3499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg___boxed(
    mut v_m_3502_: *mut leanh::LeanObject,
    mut v_a_3503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_3502_, v_a_3503_);
    leanh::lean_dec(v_a_3503_);
    leanh::lean_dec_ref(v_m_3502_);
    return v_res_3504_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
    mut v_x_3505_: *mut leanh::LeanObject,
    mut v_x_3506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_stage_u2081_3507_: u8 = 0;
    v_stage_u2081_3507_ = leanh::lean_ctor_get_uint8(
        v_x_3505_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_3507_ == 0 {
        let mut v_map_u2081_3508_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_3508_ = leanh::lean_ctor_get(v_x_3505_, 0);
        v_map_u2082_3509_ = leanh::lean_ctor_get(v_x_3505_, 1);
        v___x_3510_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_map_u2082_3509_, v_x_3506_);
        if leanh::lean_obj_tag(v___x_3510_) == 0 {
            let mut v___x_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_3508_, v_x_3506_);
            return v___x_3511_;
        } else {
            return v___x_3510_;
        }
    } else {
        let mut v_map_u2081_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3513_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_map_u2081_3512_ = leanh::lean_ctor_get(v_x_3505_, 0);
        v___x_3513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_3512_, v_x_3506_);
        return v___x_3513_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(
    mut v_x_3514_: *mut leanh::LeanObject,
    mut v_x_3515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
        v_x_3514_, v_x_3515_,
    );
    leanh::lean_dec(v_x_3515_);
    leanh::lean_dec_ref(v_x_3514_);
    return v_res_3516_;
}
pub unsafe fn _init_l_Lean_getReducibilityStatusCore___closed__2() -> *mut leanh::LeanObject
{
    let mut v___x_3519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Lean_getReducibilityStatusCore___closed__1;
    v___x_3520_ = l_Lean_getReducibilityStatusCore___closed__0;
    v___x_3521_ = l_Lean_SMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3520_,
        v___x_3519_,
    );
    return v___x_3521_;
}
pub unsafe fn lean_get_reducibility_status(
    mut v_env_3522_: *mut leanh::LeanObject,
    mut v_declName_3523_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_3525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_3529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Lean_reducibilityExtraExt;
    v_ext_3525_ = leanh::lean_ctor_get(v___x_3524_, 1);
    v_toEnvExtension_3526_ = leanh::lean_ctor_get(v_ext_3525_, 0);
    v_asyncMode_3527_ = leanh::lean_ctor_get(v_toEnvExtension_3526_, 2);
    v___x_3528_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getReducibilityStatusCore___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getReducibilityStatusCore___closed__2_once),
        _init_l_Lean_getReducibilityStatusCore___closed__2,
    );
    leanh::lean_inc_ref(v_env_3522_);
    v_m_3529_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_3528_,
        v___x_3524_,
        v_env_3522_,
        v_asyncMode_3527_,
    );
    v___x_3530_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
        v_m_3529_,
        v_declName_3523_,
    );
    leanh::lean_dec(v_m_3529_);
    if leanh::lean_obj_tag(v___x_3530_) == 1 {
        let mut v_val_3531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3532_: u8 = 0;
        leanh::lean_dec(v_declName_3523_);
        leanh::lean_dec_ref(v_env_3522_);
        v_val_3531_ = leanh::lean_ctor_get(v___x_3530_, 0);
        leanh::lean_inc(v_val_3531_);
        leanh::lean_dec_ref_known(v___x_3530_, 1);
        v___x_3532_ = (leanh::lean_unbox(v_val_3531_) as u8);
        leanh::lean_dec(v_val_3531_);
        return v___x_3532_;
    } else {
        let mut v___x_3533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3534_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_3530_);
        v___x_3533_ = leanh::lean_box(1);
        v___x_3534_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3522_, v_declName_3523_);
        if leanh::lean_obj_tag(v___x_3534_) == 0 {
            let mut v___x_3535_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_3536_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_3537_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3538_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3539_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3535_ = l_Lean_reducibilityCoreExt;
            v_toEnvExtension_3536_ = leanh::lean_ctor_get(v___x_3535_, 0);
            v_asyncMode_3537_ = leanh::lean_ctor_get(v_toEnvExtension_3536_, 2);
            leanh::lean_inc(v_declName_3523_);
            v___x_3538_ = l_Lean_PersistentEnvExtension_getState___redArg(
                v___x_3533_,
                v___x_3535_,
                v_env_3522_,
                v_asyncMode_3537_,
                v_declName_3523_,
            );
            v___x_3539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3538_, v_declName_3523_);
            leanh::lean_dec(v_declName_3523_);
            leanh::lean_dec(v___x_3538_);
            if leanh::lean_obj_tag(v___x_3539_) == 0 {
                let mut v___x_3540_: u8 = 0;
                v___x_3540_ = 1;
                return v___x_3540_;
            } else {
                let mut v_val_3541_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3542_: u8 = 0;
                v_val_3541_ = leanh::lean_ctor_get(v___x_3539_, 0);
                leanh::lean_inc(v_val_3541_);
                leanh::lean_dec_ref_known(v___x_3539_, 1);
                v___x_3542_ = (leanh::lean_unbox(v_val_3541_) as u8);
                leanh::lean_dec(v_val_3541_);
                return v___x_3542_;
            }
        } else {
            let mut v_val_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3545_: u8 = 0;
            let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3547_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3548_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3549_: u8 = 0;
            v_val_3543_ = leanh::lean_ctor_get(v___x_3534_, 0);
            leanh::lean_inc(v_val_3543_);
            leanh::lean_dec_ref_known(v___x_3534_, 1);
            v___x_3544_ = l_Lean_reducibilityCoreExt;
            v___x_3545_ = 0;
            v___x_3546_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                v___x_3533_,
                v___x_3544_,
                v_env_3522_,
                v_val_3543_,
                v___x_3545_,
            );
            leanh::lean_dec(v_val_3543_);
            leanh::lean_dec_ref(v_env_3522_);
            v___x_3547_ = leanh::lean_unsigned_to_nat(0);
            v___x_3548_ = lean_array_get_size(v___x_3546_);
            v___x_3549_ = lean_nat_dec_lt(v___x_3547_, v___x_3548_);
            if v___x_3549_ == 0 {
                let mut v___x_3550_: u8 = 0;
                leanh::lean_dec_ref(v___x_3546_);
                leanh::lean_dec(v_declName_3523_);
                v___x_3550_ = 1;
                return v___x_3550_;
            } else {
                let mut v___x_3551_: u8 = 0;
                let mut v___x_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3553_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3554_: u8 = 0;
                v___x_3551_ = 1;
                v___x_3552_ = leanh::lean_unsigned_to_nat(1);
                v___x_3553_ = lean_nat_sub(v___x_3548_, v___x_3552_);
                v___x_3554_ = lean_nat_dec_le(v___x_3547_, v___x_3553_);
                if v___x_3554_ == 0 {
                    leanh::lean_dec(v___x_3553_);
                    leanh::lean_dec_ref(v___x_3546_);
                    leanh::lean_dec(v_declName_3523_);
                    return v___x_3551_;
                } else {
                    let mut v___x_3555_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_3555_ = leanh::lean_box((v___x_3551_) as usize);
                    v___x_3556_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3556_, 0, v_declName_3523_);
                    leanh::lean_ctor_set(v___x_3556_, 1, v___x_3555_);
                    v___x_3557_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v___x_3546_, v___x_3556_, v___x_3547_, v___x_3553_);
                    leanh::lean_dec_ref_known(v___x_3556_, 2);
                    leanh::lean_dec_ref(v___x_3546_);
                    if leanh::lean_obj_tag(v___x_3557_) == 0 {
                        return v___x_3551_;
                    } else {
                        let mut v_val_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_snd_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3560_: u8 = 0;
                        v_val_3558_ = leanh::lean_ctor_get(v___x_3557_, 0);
                        leanh::lean_inc(v_val_3558_);
                        leanh::lean_dec_ref_known(v___x_3557_, 1);
                        v_snd_3559_ = leanh::lean_ctor_get(v_val_3558_, 1);
                        leanh::lean_inc(v_snd_3559_);
                        leanh::lean_dec(v_val_3558_);
                        v___x_3560_ = (leanh::lean_unbox(v_snd_3559_) as u8);
                        leanh::lean_dec(v_snd_3559_);
                        return v___x_3560_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_getReducibilityStatusCore___boxed(
    mut v_env_3561_: *mut leanh::LeanObject,
    mut v_declName_3562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3563_: u8 = 0;
    let mut v_r_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3563_ = lean_get_reducibility_status(v_env_3561_, v_declName_3562_);
    v_r_3564_ = leanh::lean_box((v_res_3563_) as usize);
    return v_r_3564_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(
    mut v_00_u03b2_3565_: *mut leanh::LeanObject,
    mut v_x_3566_: *mut leanh::LeanObject,
    mut v_x_3567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3568_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
        v_x_3566_, v_x_3567_,
    );
    return v___x_3568_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(
    mut v_00_u03b2_3569_: *mut leanh::LeanObject,
    mut v_x_3570_: *mut leanh::LeanObject,
    mut v_x_3571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(
        v_00_u03b2_3569_,
        v_x_3570_,
        v_x_3571_,
    );
    leanh::lean_dec(v_x_3571_);
    leanh::lean_dec_ref(v_x_3570_);
    return v_res_3572_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(
    mut v_as_3573_: *mut leanh::LeanObject,
    mut v_k_3574_: *mut leanh::LeanObject,
    mut v_x_3575_: *mut leanh::LeanObject,
    mut v_x_3576_: *mut leanh::LeanObject,
    mut v_x_3577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
        v_as_3573_, v_k_3574_, v_x_3575_, v_x_3576_,
    );
    return v___x_3578_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___boxed(
    mut v_as_3579_: *mut leanh::LeanObject,
    mut v_k_3580_: *mut leanh::LeanObject,
    mut v_x_3581_: *mut leanh::LeanObject,
    mut v_x_3582_: *mut leanh::LeanObject,
    mut v_x_3583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(
        v_as_3579_, v_k_3580_, v_x_3581_, v_x_3582_, v_x_3583_,
    );
    leanh::lean_dec_ref(v_k_3580_);
    leanh::lean_dec_ref(v_as_3579_);
    return v_res_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(
    mut v_00_u03b2_3585_: *mut leanh::LeanObject,
    mut v_x_3586_: *mut leanh::LeanObject,
    mut v_x_3587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_3586_, v_x_3587_);
    return v___x_3588_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_3589_: *mut leanh::LeanObject,
    mut v_x_3590_: *mut leanh::LeanObject,
    mut v_x_3591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3592_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(v_00_u03b2_3589_, v_x_3590_, v_x_3591_);
    leanh::lean_dec(v_x_3591_);
    leanh::lean_dec_ref(v_x_3590_);
    return v_res_3592_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(
    mut v_00_u03b2_3593_: *mut leanh::LeanObject,
    mut v_m_3594_: *mut leanh::LeanObject,
    mut v_a_3595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_3594_, v_a_3595_);
    return v___x_3596_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(
    mut v_00_u03b2_3597_: *mut leanh::LeanObject,
    mut v_m_3598_: *mut leanh::LeanObject,
    mut v_a_3599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(v_00_u03b2_3597_, v_m_3598_, v_a_3599_);
    leanh::lean_dec(v_a_3599_);
    leanh::lean_dec_ref(v_m_3598_);
    return v_res_3600_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3601_: *mut leanh::LeanObject,
    mut v_x_3602_: *mut leanh::LeanObject,
    mut v_x_3603_: usize,
    mut v_x_3604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_3602_, v_x_3603_, v_x_3604_);
    return v___x_3605_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3606_: *mut leanh::LeanObject,
    mut v_x_3607_: *mut leanh::LeanObject,
    mut v_x_3608_: *mut leanh::LeanObject,
    mut v_x_3609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_866__boxed_3610_: usize = 0;
    let mut v_res_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_866__boxed_3610_ = leanh::lean_unbox_usize(v_x_3608_);
    leanh::lean_dec(v_x_3608_);
    v_res_3611_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(v_00_u03b2_3606_, v_x_3607_, v_x_866__boxed_3610_, v_x_3609_);
    leanh::lean_dec(v_x_3609_);
    leanh::lean_dec_ref(v_x_3607_);
    return v_res_3611_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3612_: *mut leanh::LeanObject,
    mut v_a_3613_: *mut leanh::LeanObject,
    mut v_x_3614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_3613_, v_x_3614_);
    return v___x_3615_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3616_: *mut leanh::LeanObject,
    mut v_a_3617_: *mut leanh::LeanObject,
    mut v_x_3618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(v_00_u03b2_3616_, v_a_3617_, v_x_3618_);
    leanh::lean_dec(v_x_3618_);
    leanh::lean_dec(v_a_3617_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3620_: *mut leanh::LeanObject,
    mut v_keys_3621_: *mut leanh::LeanObject,
    mut v_vals_3622_: *mut leanh::LeanObject,
    mut v_heq_3623_: *mut leanh::LeanObject,
    mut v_i_3624_: *mut leanh::LeanObject,
    mut v_k_3625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3621_, v_vals_3622_, v_i_3624_, v_k_3625_);
    return v___x_3626_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3627_: *mut leanh::LeanObject,
    mut v_keys_3628_: *mut leanh::LeanObject,
    mut v_vals_3629_: *mut leanh::LeanObject,
    mut v_heq_3630_: *mut leanh::LeanObject,
    mut v_i_3631_: *mut leanh::LeanObject,
    mut v_k_3632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3633_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3627_, v_keys_3628_, v_vals_3629_, v_heq_3630_, v_i_3631_, v_k_3632_);
    leanh::lean_dec(v_k_3632_);
    leanh::lean_dec_ref(v_vals_3629_);
    leanh::lean_dec_ref(v_keys_3628_);
    return v_res_3633_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
    mut v_env_3634_: *mut leanh::LeanObject,
    mut v_declName_3635_: *mut leanh::LeanObject,
    mut v_status_3636_: u8,
    mut v_attrKind_3637_: u8,
    mut v_currNamespace_3638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_attrKind_3637_ == 0 {
        let mut v___x_3639_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_currNamespace_3638_);
        v___x_3639_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3634_, v_declName_3635_);
        if leanh::lean_obj_tag(v___x_3639_) == 0 {
            let mut v___x_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_3640_ = l_Lean_reducibilityCoreExt;
            v_toEnvExtension_3641_ = leanh::lean_ctor_get(v___x_3640_, 0);
            v_asyncMode_3642_ = leanh::lean_ctor_get(v_toEnvExtension_3641_, 2);
            v___x_3643_ = leanh::lean_box((v_status_3636_) as usize);
            leanh::lean_inc(v_declName_3635_);
            v___x_3644_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3644_, 0, v_declName_3635_);
            leanh::lean_ctor_set(v___x_3644_, 1, v___x_3643_);
            v___x_3645_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                v___x_3640_,
                v_env_3634_,
                v___x_3644_,
                v_asyncMode_3642_,
                v_declName_3635_,
            );
            return v___x_3645_;
        } else {
            let mut v___x_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3639_, 1);
            v___x_3646_ = l_Lean_reducibilityExtraExt;
            v___x_3647_ = leanh::lean_box((v_status_3636_) as usize);
            v___x_3648_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_3648_, 0, v_declName_3635_);
            leanh::lean_ctor_set(v___x_3648_, 1, v___x_3647_);
            v___x_3649_ =
                l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_3646_, v_env_3634_, v___x_3648_);
            return v___x_3649_;
        }
    } else {
        let mut v___x_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3650_ = l_Lean_reducibilityExtraExt;
        v___x_3651_ = leanh::lean_box((v_status_3636_) as usize);
        v___x_3652_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3652_, 0, v_declName_3635_);
        leanh::lean_ctor_set(v___x_3652_, 1, v___x_3651_);
        v___x_3653_ = l_Lean_ScopedEnvExtension_addCore___redArg(
            v_env_3634_,
            v___x_3650_,
            v___x_3652_,
            v_attrKind_3637_,
            v_currNamespace_3638_,
        );
        return v___x_3653_;
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore___boxed(
    mut v_env_3654_: *mut leanh::LeanObject,
    mut v_declName_3655_: *mut leanh::LeanObject,
    mut v_status_3656_: *mut leanh::LeanObject,
    mut v_attrKind_3657_: *mut leanh::LeanObject,
    mut v_currNamespace_3658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_boxed_3659_: u8 = 0;
    let mut v_attrKind_boxed_3660_: u8 = 0;
    let mut v_res_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_boxed_3659_ = (leanh::lean_unbox(v_status_3656_) as u8);
    v_attrKind_boxed_3660_ = (leanh::lean_unbox(v_attrKind_3657_) as u8);
    v_res_3661_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
        v_env_3654_,
        v_declName_3655_,
        v_status_boxed_3659_,
        v_attrKind_boxed_3660_,
        v_currNamespace_3658_,
    );
    return v_res_3661_;
}
pub unsafe fn lean_set_reducibility_status(
    mut v_env_3662_: *mut leanh::LeanObject,
    mut v_declName_3663_: *mut leanh::LeanObject,
    mut v_status_3664_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_3665_: u8 = 0;
    let mut v___x_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = 0;
    v___x_3666_ = leanh::lean_box(0);
    v___x_3667_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
        v_env_3662_,
        v_declName_3663_,
        v_status_3664_,
        v___x_3665_,
        v___x_3666_,
    );
    return v___x_3667_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusImp___boxed(
    mut v_env_3668_: *mut leanh::LeanObject,
    mut v_declName_3669_: *mut leanh::LeanObject,
    mut v_status_3670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_boxed_3671_: u8 = 0;
    let mut v_res_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_boxed_3671_ = (leanh::lean_unbox(v_status_3670_) as u8);
    v_res_3672_ = lean_set_reducibility_status(v_env_3668_, v_declName_3669_, v_status_boxed_3671_);
    return v_res_3672_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(
    mut v_name_3673_: *mut leanh::LeanObject,
    mut v_decl_3674_: *mut leanh::LeanObject,
    mut v_ref_3675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defValue_3677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_unused_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3677_ = leanh::lean_ctor_get(v_decl_3674_, 0);
                v_descr_3678_ = leanh::lean_ctor_get(v_decl_3674_, 1);
                v_deprecation_x3f_3679_ = leanh::lean_ctor_get(v_decl_3674_, 2);
                v___x_3680_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3681_ = (leanh::lean_unbox(v_defValue_3677_) as u8);
                leanh::lean_ctor_set_uint8(v___x_3680_, 0 as u32, v___x_3681_);
                leanh::lean_inc(v_deprecation_x3f_3679_);
                leanh::lean_inc_ref(v_descr_3678_);
                leanh::lean_inc_n(v_name_3673_, 2);
                v___x_3682_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                leanh::lean_ctor_set(v___x_3682_, 0, v_name_3673_);
                leanh::lean_ctor_set(v___x_3682_, 1, v_ref_3675_);
                leanh::lean_ctor_set(v___x_3682_, 2, v___x_3680_);
                leanh::lean_ctor_set(v___x_3682_, 3, v_descr_3678_);
                leanh::lean_ctor_set(v___x_3682_, 4, v_deprecation_x3f_3679_);
                v___x_3683_ = lean_register_option(v_name_3673_, v___x_3682_);
                if leanh::lean_obj_tag(v___x_3683_) == 0 {
                    v_isSharedCheck_3691_ = (!leanh::lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v_unused_3692_ = leanh::lean_ctor_get(v___x_3683_, 0);
                        leanh::lean_dec(v_unused_3692_);
                        v___x_3685_ = v___x_3683_;
                        v_isShared_3686_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_3683_);
                        v___x_3685_ = leanh::lean_box(0);
                        v_isShared_3686_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_name_3673_);
                    v_a_3693_ = leanh::lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3700_ = (!leanh::lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v___x_3695_ = v___x_3683_;
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3693_);
                        leanh::lean_dec(v___x_3683_);
                        v___x_3695_ = leanh::lean_box(0);
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_defValue_3677_);
                v___x_3687_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3687_, 0, v_name_3673_);
                leanh::lean_ctor_set(v___x_3687_, 1, v_defValue_3677_);
                if v_isShared_3686_ == 0 {
                    leanh::lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
                    v___x_3689_ = v_reuseFailAlloc_3690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3689_;
            }
            3 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3701_: *mut leanh::LeanObject,
    mut v_decl_3702_: *mut leanh::LeanObject,
    mut v_ref_3703_: *mut leanh::LeanObject,
    mut v_a_3704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v_name_3701_, v_decl_3702_, v_ref_3703_);
    leanh::lean_dec_ref(v_decl_3702_);
    return v_res_3705_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_()
-> *mut leanh::LeanObject {
    let mut v___x_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3720_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3721_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3722_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3723_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v___x_3720_, v___x_3721_, v___x_3722_);
    return v___x_3723_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(
    mut v_a_3724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
    return v_res_3725_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(
    mut v_opts_3726_: *mut leanh::LeanObject,
    mut v_opt_3727_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_3728_ = leanh::lean_ctor_get(v_opt_3727_, 0);
    v_defValue_3729_ = leanh::lean_ctor_get(v_opt_3727_, 1);
    v_map_3730_ = leanh::lean_ctor_get(v_opts_3726_, 0);
    v___x_3731_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3730_,
            v_name_3728_,
        );
    if leanh::lean_obj_tag(v___x_3731_) == 0 {
        let mut v___x_3732_: u8 = 0;
        v___x_3732_ = (leanh::lean_unbox(v_defValue_3729_) as u8);
        return v___x_3732_;
    } else {
        let mut v_val_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_3733_ = leanh::lean_ctor_get(v___x_3731_, 0);
        leanh::lean_inc(v_val_3733_);
        leanh::lean_dec_ref_known(v___x_3731_, 1);
        if leanh::lean_obj_tag(v_val_3733_) == 1 {
            let mut v_v_3734_: u8 = 0;
            v_v_3734_ = leanh::lean_ctor_get_uint8(v_val_3733_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_3733_, 0);
            return v_v_3734_;
        } else {
            let mut v___x_3735_: u8 = 0;
            leanh::lean_dec(v_val_3733_);
            v___x_3735_ = (leanh::lean_unbox(v_defValue_3729_) as u8);
            return v___x_3735_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(
    mut v_opts_3736_: *mut leanh::LeanObject,
    mut v_opt_3737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3738_: u8 = 0;
    let mut v_r_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3738_ =
        l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(
            v_opts_3736_,
            v_opt_3737_,
        );
    leanh::lean_dec_ref(v_opt_3737_);
    leanh::lean_dec_ref(v_opts_3736_);
    v_r_3739_ = leanh::lean_box((v_res_3738_) as usize);
    return v_r_3739_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3740_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_3740_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3741_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
    v___x_3742_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3742_, 0, v___x_3741_);
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3743_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
    v___x_3744_ = leanh::lean_unsigned_to_nat(0);
    v___x_3745_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_3745_, 0, v___x_3744_);
    leanh::lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    leanh::lean_ctor_set(v___x_3745_, 2, v___x_3744_);
    leanh::lean_ctor_set(v___x_3745_, 3, v___x_3744_);
    leanh::lean_ctor_set(v___x_3745_, 4, v___x_3743_);
    leanh::lean_ctor_set(v___x_3745_, 5, v___x_3743_);
    leanh::lean_ctor_set(v___x_3745_, 6, v___x_3743_);
    leanh::lean_ctor_set(v___x_3745_, 7, v___x_3743_);
    leanh::lean_ctor_set(v___x_3745_, 8, v___x_3743_);
    leanh::lean_ctor_set(v___x_3745_, 9, v___x_3743_);
    return v___x_3745_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3746_ = leanh::lean_unsigned_to_nat(32);
    v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
    v___x_3748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3748_, 0, v___x_3747_);
    return v___x_3748_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3749_: usize = 0;
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3749_ = 5usize;
    v___x_3750_ = leanh::lean_unsigned_to_nat(0);
    v___x_3751_ = leanh::lean_unsigned_to_nat(32);
    v___x_3752_ = lean_mk_empty_array_with_capacity(v___x_3751_);
    v___x_3753_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3);
    v___x_3754_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_3754_, 0, v___x_3753_);
    leanh::lean_ctor_set(v___x_3754_, 1, v___x_3752_);
    leanh::lean_ctor_set(v___x_3754_, 2, v___x_3750_);
    leanh::lean_ctor_set(v___x_3754_, 3, v___x_3750_);
    leanh::lean_ctor_set_usize(v___x_3754_, 4, v___x_3749_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3755_ = leanh::lean_box(1);
    v___x_3756_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
    v___x_3757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
    v___x_3758_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3758_, 0, v___x_3757_);
    leanh::lean_ctor_set(v___x_3758_, 1, v___x_3756_);
    leanh::lean_ctor_set(v___x_3758_, 2, v___x_3755_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(
    mut v_msgData_3759_: *mut leanh::LeanObject,
    mut v___y_3760_: *mut leanh::LeanObject,
    mut v___y_3761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3763_ = lean_st_ref_get(v___y_3761_);
    v_env_3764_ = leanh::lean_ctor_get(v___x_3763_, 0);
    leanh::lean_inc_ref(v_env_3764_);
    leanh::lean_dec(v___x_3763_);
    v_options_3765_ = leanh::lean_ctor_get(v___y_3760_, 2);
    v___x_3766_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
    v___x_3767_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
    leanh::lean_inc_ref(v_options_3765_);
    v___x_3768_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_3768_, 0, v_env_3764_);
    leanh::lean_ctor_set(v___x_3768_, 1, v___x_3766_);
    leanh::lean_ctor_set(v___x_3768_, 2, v___x_3767_);
    leanh::lean_ctor_set(v___x_3768_, 3, v_options_3765_);
    v___x_3769_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3769_, 0, v___x_3768_);
    leanh::lean_ctor_set(v___x_3769_, 1, v_msgData_3759_);
    v___x_3770_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3770_, 0, v___x_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(
    mut v_msgData_3771_: *mut leanh::LeanObject,
    mut v___y_3772_: *mut leanh::LeanObject,
    mut v___y_3773_: *mut leanh::LeanObject,
    mut v___y_3774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3775_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msgData_3771_, v___y_3772_, v___y_3773_);
    leanh::lean_dec(v___y_3773_);
    leanh::lean_dec_ref(v___y_3772_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(
    mut v_msg_3776_: *mut leanh::LeanObject,
    mut v___y_3777_: *mut leanh::LeanObject,
    mut v___y_3778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3780_ = leanh::lean_ctor_get(v___y_3777_, 5);
                v___x_3781_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msg_3776_, v___y_3777_, v___y_3778_);
                v_a_3782_ = leanh::lean_ctor_get(v___x_3781_, 0);
                v_isSharedCheck_3790_ = (!leanh::lean_is_exclusive(v___x_3781_)) as u8;
                if v_isSharedCheck_3790_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    v_isShared_3785_ = v_isSharedCheck_3790_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3782_);
                    leanh::lean_dec(v___x_3781_);
                    v___x_3784_ = leanh::lean_box(0);
                    v_isShared_3785_ = v_isSharedCheck_3790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_3780_);
                v___x_3786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3786_, 0, v_ref_3780_);
                leanh::lean_ctor_set(v___x_3786_, 1, v_a_3782_);
                if v_isShared_3785_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3784_, 1);
                    leanh::lean_ctor_set(v___x_3784_, 0, v___x_3786_);
                    v___x_3788_ = v___x_3784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
                    v___x_3788_ = v_reuseFailAlloc_3789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg___boxed(
    mut v_msg_3791_: *mut leanh::LeanObject,
    mut v___y_3792_: *mut leanh::LeanObject,
    mut v___y_3793_: *mut leanh::LeanObject,
    mut v___y_3794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_3791_, v___y_3792_, v___y_3793_);
    leanh::lean_dec(v___y_3793_);
    leanh::lean_dec_ref(v___y_3792_);
    return v_res_3795_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(
    mut v_ref_3796_: *mut leanh::LeanObject,
    mut v_msg_3797_: *mut leanh::LeanObject,
    mut v___y_3798_: *mut leanh::LeanObject,
    mut v___y_3799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3813_: u8 = 0;
    let mut v_cancelTk_x3f_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3815_: u8 = 0;
    let mut v_inheritedTraceOptions_3816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3801_ = leanh::lean_ctor_get(v___y_3798_, 0);
    v_fileMap_3802_ = leanh::lean_ctor_get(v___y_3798_, 1);
    v_options_3803_ = leanh::lean_ctor_get(v___y_3798_, 2);
    v_currRecDepth_3804_ = leanh::lean_ctor_get(v___y_3798_, 3);
    v_maxRecDepth_3805_ = leanh::lean_ctor_get(v___y_3798_, 4);
    v_ref_3806_ = leanh::lean_ctor_get(v___y_3798_, 5);
    v_currNamespace_3807_ = leanh::lean_ctor_get(v___y_3798_, 6);
    v_openDecls_3808_ = leanh::lean_ctor_get(v___y_3798_, 7);
    v_initHeartbeats_3809_ = leanh::lean_ctor_get(v___y_3798_, 8);
    v_maxHeartbeats_3810_ = leanh::lean_ctor_get(v___y_3798_, 9);
    v_quotContext_3811_ = leanh::lean_ctor_get(v___y_3798_, 10);
    v_currMacroScope_3812_ = leanh::lean_ctor_get(v___y_3798_, 11);
    v_diag_3813_ = leanh::lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3814_ = leanh::lean_ctor_get(v___y_3798_, 12);
    v_suppressElabErrors_3815_ = leanh::lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3816_ = leanh::lean_ctor_get(v___y_3798_, 13);
    v_ref_3817_ = l_Lean_replaceRef(v_ref_3796_, v_ref_3806_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_3816_);
    leanh::lean_inc(v_cancelTk_x3f_3814_);
    leanh::lean_inc(v_currMacroScope_3812_);
    leanh::lean_inc(v_quotContext_3811_);
    leanh::lean_inc(v_maxHeartbeats_3810_);
    leanh::lean_inc(v_initHeartbeats_3809_);
    leanh::lean_inc(v_openDecls_3808_);
    leanh::lean_inc(v_currNamespace_3807_);
    leanh::lean_inc(v_maxRecDepth_3805_);
    leanh::lean_inc(v_currRecDepth_3804_);
    leanh::lean_inc_ref(v_options_3803_);
    leanh::lean_inc_ref(v_fileMap_3802_);
    leanh::lean_inc_ref(v_fileName_3801_);
    v___x_3818_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_3818_, 0, v_fileName_3801_);
    leanh::lean_ctor_set(v___x_3818_, 1, v_fileMap_3802_);
    leanh::lean_ctor_set(v___x_3818_, 2, v_options_3803_);
    leanh::lean_ctor_set(v___x_3818_, 3, v_currRecDepth_3804_);
    leanh::lean_ctor_set(v___x_3818_, 4, v_maxRecDepth_3805_);
    leanh::lean_ctor_set(v___x_3818_, 5, v_ref_3817_);
    leanh::lean_ctor_set(v___x_3818_, 6, v_currNamespace_3807_);
    leanh::lean_ctor_set(v___x_3818_, 7, v_openDecls_3808_);
    leanh::lean_ctor_set(v___x_3818_, 8, v_initHeartbeats_3809_);
    leanh::lean_ctor_set(v___x_3818_, 9, v_maxHeartbeats_3810_);
    leanh::lean_ctor_set(v___x_3818_, 10, v_quotContext_3811_);
    leanh::lean_ctor_set(v___x_3818_, 11, v_currMacroScope_3812_);
    leanh::lean_ctor_set(v___x_3818_, 12, v_cancelTk_x3f_3814_);
    leanh::lean_ctor_set(v___x_3818_, 13, v_inheritedTraceOptions_3816_);
    leanh::lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_3813_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3815_,
    );
    v___x_3819_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_3797_, v___x_3818_, v___y_3799_);
    leanh::lean_dec_ref_known(v___x_3818_, 14);
    return v___x_3819_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(
    mut v_ref_3820_: *mut leanh::LeanObject,
    mut v_msg_3821_: *mut leanh::LeanObject,
    mut v___y_3822_: *mut leanh::LeanObject,
    mut v___y_3823_: *mut leanh::LeanObject,
    mut v___y_3824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3820_, v_msg_3821_, v___y_3822_, v___y_3823_);
    leanh::lean_dec(v___y_3823_);
    leanh::lean_dec_ref(v___y_3822_);
    leanh::lean_dec(v_ref_3820_);
    return v_res_3825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0;
    v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
    return v___x_3828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2;
    v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
    return v___x_3831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
    return v___x_3834_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
    return v___x_3837_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_3840_ = l_Lean_stringToMessageData(v___x_3839_);
    return v___x_3840_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
    return v___x_3843_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(
    mut v_msg_3847_: *mut leanh::LeanObject,
    mut v_declHint_3848_: *mut leanh::LeanObject,
    mut v___y_3849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v_isExporting_3854_: u8 = 0;
    let mut v___x_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3851_ = lean_st_ref_get(v___y_3849_);
                v_env_3852_ = leanh::lean_ctor_get(v___x_3851_, 0);
                leanh::lean_inc_ref(v_env_3852_);
                leanh::lean_dec(v___x_3851_);
                v___x_3853_ = l_Lean_Name_isAnonymous(v_declHint_3848_);
                if v___x_3853_ == 0 {
                    v_isExporting_3854_ = leanh::lean_ctor_get_uint8(
                        v_env_3852_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3854_ == 0 {
                        leanh::lean_dec_ref(v_env_3852_);
                        leanh::lean_dec(v_declHint_3848_);
                        v___x_3855_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3855_, 0, v_msg_3847_);
                        return v___x_3855_;
                    } else {
                        leanh::lean_inc_ref(v_env_3852_);
                        v___x_3856_ = l_Lean_Environment_setExporting(v_env_3852_, v___x_3853_);
                        leanh::lean_inc(v_declHint_3848_);
                        leanh::lean_inc_ref(v___x_3856_);
                        v___x_3857_ = l_Lean_Environment_contains(
                            v___x_3856_,
                            v_declHint_3848_,
                            v_isExporting_3854_,
                        );
                        if v___x_3857_ == 0 {
                            leanh::lean_dec_ref(v___x_3856_);
                            leanh::lean_dec_ref(v_env_3852_);
                            leanh::lean_dec(v_declHint_3848_);
                            v___x_3858_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3858_, 0, v_msg_3847_);
                            return v___x_3858_;
                        } else {
                            v___x_3859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
                            v___x_3860_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
                            v___x_3861_ = l_Lean_Options_empty;
                            v___x_3862_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_3862_, 0, v___x_3856_);
                            leanh::lean_ctor_set(v___x_3862_, 1, v___x_3859_);
                            leanh::lean_ctor_set(v___x_3862_, 2, v___x_3860_);
                            leanh::lean_ctor_set(v___x_3862_, 3, v___x_3861_);
                            leanh::lean_inc(v_declHint_3848_);
                            v___x_3863_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3848_, v___x_3853_);
                            v_c_3864_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_3864_, 0, v___x_3862_);
                            leanh::lean_ctor_set(v_c_3864_, 1, v___x_3863_);
                            v___x_3865_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3852_,
                                v_declHint_3848_,
                            );
                            if leanh::lean_obj_tag(v___x_3865_) == 0 {
                                leanh::lean_dec_ref(v_env_3852_);
                                leanh::lean_dec(v_declHint_3848_);
                                v___x_3866_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                                v___x_3867_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                                leanh::lean_ctor_set(v___x_3867_, 1, v_c_3864_);
                                v___x_3868_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
                                v___x_3869_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3869_, 0, v___x_3867_);
                                leanh::lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                                v___x_3870_ = l_Lean_MessageData_note(v___x_3869_);
                                v___x_3871_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3871_, 0, v_msg_3847_);
                                leanh::lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                                v___x_3872_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_3872_, 0, v___x_3871_);
                                return v___x_3872_;
                            } else {
                                v_val_3873_ = leanh::lean_ctor_get(v___x_3865_, 0);
                                v_isSharedCheck_3908_ =
                                    (!leanh::lean_is_exclusive(v___x_3865_)) as u8;
                                if v_isSharedCheck_3908_ == 0 {
                                    v___x_3875_ = v___x_3865_;
                                    v_isShared_3876_ = v_isSharedCheck_3908_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_3873_);
                                    leanh::lean_dec(v___x_3865_);
                                    v___x_3875_ = leanh::lean_box(0);
                                    v_isShared_3876_ = v_isSharedCheck_3908_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_3852_);
                    leanh::lean_dec(v_declHint_3848_);
                    v___x_3909_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3909_, 0, v_msg_3847_);
                    return v___x_3909_;
                }
            }
            1 => {
                v___x_3877_ = leanh::lean_box(0);
                v___x_3878_ = l_Lean_Environment_header(v_env_3852_);
                leanh::lean_dec_ref(v_env_3852_);
                v___x_3879_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3878_);
                v_mod_3880_ = lean_array_get(v___x_3877_, v___x_3879_, v_val_3873_);
                leanh::lean_dec(v_val_3873_);
                leanh::lean_dec_ref(v___x_3879_);
                v___x_3881_ = l_Lean_isPrivateName(v_declHint_3848_);
                leanh::lean_dec(v_declHint_3848_);
                if v___x_3881_ == 0 {
                    v___x_3882_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_3883_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3883_, 0, v___x_3882_);
                    leanh::lean_ctor_set(v___x_3883_, 1, v_c_3864_);
                    v___x_3884_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_3885_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3885_, 0, v___x_3883_);
                    leanh::lean_ctor_set(v___x_3885_, 1, v___x_3884_);
                    v___x_3886_ = l_Lean_MessageData_ofName(v_mod_3880_);
                    v___x_3887_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3887_, 0, v___x_3885_);
                    leanh::lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                    v___x_3888_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_3889_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3889_, 0, v___x_3887_);
                    leanh::lean_ctor_set(v___x_3889_, 1, v___x_3888_);
                    v___x_3890_ = l_Lean_MessageData_note(v___x_3889_);
                    v___x_3891_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3891_, 0, v_msg_3847_);
                    leanh::lean_ctor_set(v___x_3891_, 1, v___x_3890_);
                    if v_isShared_3876_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3875_, 0);
                        leanh::lean_ctor_set(v___x_3875_, 0, v___x_3891_);
                        v___x_3893_ = v___x_3875_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
                        v___x_3893_ = v_reuseFailAlloc_3894_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3895_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                    v___x_3896_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                    leanh::lean_ctor_set(v___x_3896_, 1, v_c_3864_);
                    v___x_3897_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_3898_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3898_, 0, v___x_3896_);
                    leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                    v___x_3899_ = l_Lean_MessageData_ofName(v_mod_3880_);
                    v___x_3900_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3900_, 0, v___x_3898_);
                    leanh::lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                    v___x_3901_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_3902_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                    leanh::lean_ctor_set(v___x_3902_, 1, v___x_3901_);
                    v___x_3903_ = l_Lean_MessageData_note(v___x_3902_);
                    v___x_3904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3904_, 0, v_msg_3847_);
                    leanh::lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                    if v_isShared_3876_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_3875_, 0);
                        leanh::lean_ctor_set(v___x_3875_, 0, v___x_3904_);
                        v___x_3906_ = v___x_3875_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3907_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
                        v___x_3906_ = v_reuseFailAlloc_3907_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3893_;
            }
            3 => {
                return v___x_3906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_3910_: *mut leanh::LeanObject,
    mut v_declHint_3911_: *mut leanh::LeanObject,
    mut v___y_3912_: *mut leanh::LeanObject,
    mut v___y_3913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3914_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3910_, v_declHint_3911_, v___y_3912_);
    leanh::lean_dec(v___y_3912_);
    return v_res_3914_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(
    mut v_msg_3915_: *mut leanh::LeanObject,
    mut v_declHint_3916_: *mut leanh::LeanObject,
    mut v___y_3917_: *mut leanh::LeanObject,
    mut v___y_3918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3915_, v_declHint_3916_, v___y_3918_);
                v_a_3921_ = leanh::lean_ctor_get(v___x_3920_, 0);
                v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v___x_3920_)) as u8;
                if v_isSharedCheck_3930_ == 0 {
                    v___x_3923_ = v___x_3920_;
                    v_isShared_3924_ = v_isSharedCheck_3930_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3921_);
                    leanh::lean_dec(v___x_3920_);
                    v___x_3923_ = leanh::lean_box(0);
                    v_isShared_3924_ = v_isSharedCheck_3930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3925_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3926_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3926_, 0, v___x_3925_);
                leanh::lean_ctor_set(v___x_3926_, 1, v_a_3921_);
                if v_isShared_3924_ == 0 {
                    leanh::lean_ctor_set(v___x_3923_, 0, v___x_3926_);
                    v___x_3928_ = v___x_3923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
                    v___x_3928_ = v_reuseFailAlloc_3929_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8___boxed(
    mut v_msg_3931_: *mut leanh::LeanObject,
    mut v_declHint_3932_: *mut leanh::LeanObject,
    mut v___y_3933_: *mut leanh::LeanObject,
    mut v___y_3934_: *mut leanh::LeanObject,
    mut v___y_3935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3931_, v_declHint_3932_, v___y_3933_, v___y_3934_);
    leanh::lean_dec(v___y_3934_);
    leanh::lean_dec_ref(v___y_3933_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(
    mut v_ref_3937_: *mut leanh::LeanObject,
    mut v_msg_3938_: *mut leanh::LeanObject,
    mut v_declHint_3939_: *mut leanh::LeanObject,
    mut v___y_3940_: *mut leanh::LeanObject,
    mut v___y_3941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3938_, v_declHint_3939_, v___y_3940_, v___y_3941_);
    v_a_3944_ = leanh::lean_ctor_get(v___x_3943_, 0);
    leanh::lean_inc(v_a_3944_);
    leanh::lean_dec_ref(v___x_3943_);
    v___x_3945_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3937_, v_a_3944_, v___y_3940_, v___y_3941_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_ref_3946_: *mut leanh::LeanObject,
    mut v_msg_3947_: *mut leanh::LeanObject,
    mut v_declHint_3948_: *mut leanh::LeanObject,
    mut v___y_3949_: *mut leanh::LeanObject,
    mut v___y_3950_: *mut leanh::LeanObject,
    mut v___y_3951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3946_, v_msg_3947_, v_declHint_3948_, v___y_3949_, v___y_3950_);
    leanh::lean_dec(v___y_3950_);
    leanh::lean_dec_ref(v___y_3949_);
    leanh::lean_dec(v_ref_3946_);
    return v_res_3952_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3954_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3955_ = l_Lean_stringToMessageData(v___x_3954_);
    return v___x_3955_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(
    mut v_ref_3959_: *mut leanh::LeanObject,
    mut v_constName_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3964_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3965_ = 0;
    leanh::lean_inc(v_constName_3960_);
    v___x_3966_ = l_Lean_MessageData_ofConstName(v_constName_3960_, v___x_3965_);
    v___x_3967_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3967_, 0, v___x_3964_);
    leanh::lean_ctor_set(v___x_3967_, 1, v___x_3966_);
    v___x_3968_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_3969_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3969_, 0, v___x_3967_);
    leanh::lean_ctor_set(v___x_3969_, 1, v___x_3968_);
    v___x_3970_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3959_, v___x_3969_, v_constName_3960_, v___y_3961_, v___y_3962_);
    return v___x_3970_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_ref_3971_: *mut leanh::LeanObject,
    mut v_constName_3972_: *mut leanh::LeanObject,
    mut v___y_3973_: *mut leanh::LeanObject,
    mut v___y_3974_: *mut leanh::LeanObject,
    mut v___y_3975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_3971_, v_constName_3972_, v___y_3973_, v___y_3974_);
    leanh::lean_dec(v___y_3974_);
    leanh::lean_dec_ref(v___y_3973_);
    leanh::lean_dec(v_ref_3971_);
    return v_res_3976_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(
    mut v_constName_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_3981_ = leanh::lean_ctor_get(v___y_3978_, 5);
    v___x_3982_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_3981_, v_constName_3977_, v___y_3978_, v___y_3979_);
    return v___x_3982_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(
    mut v_constName_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_3983_, v___y_3984_, v___y_3985_);
    leanh::lean_dec(v___y_3985_);
    leanh::lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(
    mut v_constName_3988_: *mut leanh::LeanObject,
    mut v___y_3989_: *mut leanh::LeanObject,
    mut v___y_3990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: u8 = 0;
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3992_ = lean_st_ref_get(v___y_3990_);
                v_env_3993_ = leanh::lean_ctor_get(v___x_3992_, 0);
                leanh::lean_inc_ref(v_env_3993_);
                leanh::lean_dec(v___x_3992_);
                v___x_3994_ = 0;
                leanh::lean_inc(v_constName_3988_);
                v___x_3995_ =
                    l_Lean_Environment_find_x3f(v_env_3993_, v_constName_3988_, v___x_3994_);
                if leanh::lean_obj_tag(v___x_3995_) == 0 {
                    v___x_3996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_3988_, v___y_3989_, v___y_3990_);
                    return v___x_3996_;
                } else {
                    leanh::lean_dec(v_constName_3988_);
                    v_val_3997_ = leanh::lean_ctor_get(v___x_3995_, 0);
                    v_isSharedCheck_4004_ = (!leanh::lean_is_exclusive(v___x_3995_)) as u8;
                    if v_isSharedCheck_4004_ == 0 {
                        v___x_3999_ = v___x_3995_;
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3997_);
                        leanh::lean_dec(v___x_3995_);
                        v___x_3999_ = leanh::lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4000_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3999_, 0);
                    v___x_4002_ = v___x_3999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_val_3997_);
                    v___x_4002_ = v_reuseFailAlloc_4003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4002_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2___boxed(
    mut v_constName_4005_: *mut leanh::LeanObject,
    mut v___y_4006_: *mut leanh::LeanObject,
    mut v___y_4007_: *mut leanh::LeanObject,
    mut v___y_4008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4009_ =
        l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(
            v_constName_4005_,
            v___y_4006_,
            v___y_4007_,
        );
    leanh::lean_dec(v___y_4007_);
    leanh::lean_dec_ref(v___y_4006_);
    return v_res_4009_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4011_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0;
    v___x_4012_ = l_Lean_stringToMessageData(v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4014_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2;
    v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
    return v___x_4015_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4017_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4;
    v___x_4018_ = l_Lean_stringToMessageData(v___x_4017_);
    return v___x_4018_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4020_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6;
    v___x_4021_ = l_Lean_stringToMessageData(v___x_4020_);
    return v___x_4021_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8;
    v___x_4024_ = l_Lean_stringToMessageData(v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4026_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10;
    v___x_4027_ = l_Lean_stringToMessageData(v___x_4026_);
    return v___x_4027_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4029_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12;
    v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_4032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4032_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14;
    v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
    return v___x_4033_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16;
    v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
    return v___x_4036_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4038_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18;
    v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
    return v___x_4039_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4041_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20;
    v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
    return v___x_4042_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4044_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22;
    v___x_4045_ = l_Lean_stringToMessageData(v___x_4044_);
    return v___x_4045_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4047_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24;
    v___x_4048_ = l_Lean_stringToMessageData(v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4050_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26;
    v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
    return v___x_4051_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4053_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28;
    v___x_4054_ = l_Lean_stringToMessageData(v___x_4053_);
    return v___x_4054_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31()
-> *mut leanh::LeanObject {
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30;
    v___x_4057_ = l_Lean_stringToMessageData(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4059_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32;
    v___x_4060_ = l_Lean_stringToMessageData(v___x_4059_);
    return v___x_4060_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34;
    v___x_4063_ = l_Lean_stringToMessageData(v___x_4062_);
    return v___x_4063_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37()
-> *mut leanh::LeanObject {
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4065_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36;
    v___x_4066_ = l_Lean_stringToMessageData(v___x_4065_);
    return v___x_4066_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4068_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38;
    v___x_4069_ = l_Lean_stringToMessageData(v___x_4068_);
    return v___x_4069_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41()
-> *mut leanh::LeanObject {
    let mut v___x_4071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4071_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40;
    v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
    return v___x_4072_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(
    mut v_declName_4073_: *mut leanh::LeanObject,
    mut v_status_4074_: u8,
    mut v_suffix_4075_: *mut leanh::LeanObject,
    mut v_attrKind_4076_: u8,
    mut v___y_4077_: *mut leanh::LeanObject,
    mut v___y_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___y_4102_: u8 = 0;
    let mut v___y_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4150_: u8 = 0;
    let mut v___y_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: u8 = 0;
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4098_ = leanh::lean_ctor_get(v___y_4077_, 2);
                v___x_4099_ = l_Lean_allowUnsafeReducibility;
                v___x_4100_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_options_4098_, v___x_4099_);
                if v___x_4100_ == 0 {
                    leanh::lean_inc(v_declName_4073_);
                    v___x_4218_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_declName_4073_, v___y_4077_, v___y_4078_);
                    if leanh::lean_obj_tag(v___x_4218_) == 0 {
                        v_a_4219_ = leanh::lean_ctor_get(v___x_4218_, 0);
                        leanh::lean_inc(v_a_4219_);
                        leanh::lean_dec_ref_known(v___x_4218_, 1);
                        v___x_4220_ = l_Lean_ConstantInfo_isDefinition(v_a_4219_);
                        leanh::lean_dec(v_a_4219_);
                        if v___x_4220_ == 0 {
                            v___x_4221_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
                            v___x_4222_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4220_);
                            v___x_4223_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4223_, 0, v___x_4221_);
                            leanh::lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                            v___x_4224_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41);
                            v___x_4225_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4225_, 0, v___x_4223_);
                            leanh::lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                            v___x_4226_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4226_, 0, v___x_4225_);
                            leanh::lean_ctor_set(v___x_4226_, 1, v_suffix_4075_);
                            v___x_4227_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4226_, v___y_4077_, v___y_4078_);
                            return v___x_4227_;
                        } else {
                            v___y_4160_ = v___y_4077_;
                            v___y_4161_ = v___y_4078_;
                            state = 9;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_suffix_4075_);
                        leanh::lean_dec(v_declName_4073_);
                        v_a_4228_ = leanh::lean_ctor_get(v___x_4218_, 0);
                        v_isSharedCheck_4235_ =
                            (!leanh::lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4235_ == 0 {
                            v___x_4230_ = v___x_4218_;
                            v_isShared_4231_ = v_isSharedCheck_4235_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4228_);
                            leanh::lean_dec(v___x_4218_);
                            v___x_4230_ = leanh::lean_box(0);
                            v_isShared_4231_ = v_isSharedCheck_4235_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_suffix_4075_);
                    leanh::lean_dec(v_declName_4073_);
                    v___x_4236_ = leanh::lean_box(0);
                    v___x_4237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                    return v___x_4237_;
                }
            }
            1 => {
                v___x_4081_ = leanh::lean_box(0);
                v___x_4082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4082_, 0, v___x_4081_);
                return v___x_4082_;
            }
            2 => {
                v___x_4084_ = leanh::lean_box(0);
                v___x_4085_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4085_, 0, v___x_4084_);
                return v___x_4085_;
            }
            3 => {
                v___x_4087_ = leanh::lean_box(0);
                v___x_4088_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4088_, 0, v___x_4087_);
                return v___x_4088_;
            }
            4 => {
                v___x_4090_ = leanh::lean_box(0);
                v___x_4091_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4091_, 0, v___x_4090_);
                return v___x_4091_;
            }
            5 => {
                v___x_4093_ = leanh::lean_box(0);
                v___x_4094_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4094_, 0, v___x_4093_);
                return v___x_4094_;
            }
            6 => {
                v___x_4096_ = leanh::lean_box(0);
                v___x_4097_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4097_, 0, v___x_4096_);
                return v___x_4097_;
            }
            7 => match v_status_4074_ {
                0 => {
                    if v___y_4102_ == 1 {
                        leanh::lean_dec_ref(v_suffix_4075_);
                        leanh::lean_dec(v_declName_4073_);
                        state = 6;
                        continue;
                    } else {
                        if v___x_4100_ == 0 {
                            v___x_4105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
                            v___x_4106_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4107_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4107_, 0, v___x_4105_);
                            leanh::lean_ctor_set(v___x_4107_, 1, v___x_4106_);
                            v___x_4108_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
                            v___x_4109_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4109_, 0, v___x_4107_);
                            leanh::lean_ctor_set(v___x_4109_, 1, v___x_4108_);
                            v___x_4110_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
                            v___x_4112_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4112_, 0, v___x_4109_);
                            leanh::lean_ctor_set(v___x_4112_, 1, v___x_4111_);
                            v___x_4113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4114_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4114_, 0, v___x_4112_);
                            leanh::lean_ctor_set(v___x_4114_, 1, v___x_4113_);
                            v___x_4115_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4115_, 0, v___x_4114_);
                            leanh::lean_ctor_set(v___x_4115_, 1, v_suffix_4075_);
                            v___x_4116_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4115_, v___y_4103_, v___y_4104_);
                            return v___x_4116_;
                        } else {
                            leanh::lean_dec_ref(v_suffix_4075_);
                            leanh::lean_dec(v_declName_4073_);
                            state = 6;
                            continue;
                        }
                    }
                }
                1 => {
                    v___x_4117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
                    v___x_4118_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                    v___x_4119_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4119_, 0, v___x_4117_);
                    leanh::lean_ctor_set(v___x_4119_, 1, v___x_4118_);
                    v___x_4120_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
                    v___x_4121_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4121_, 0, v___x_4119_);
                    leanh::lean_ctor_set(v___x_4121_, 1, v___x_4120_);
                    v___x_4122_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4122_, 0, v___x_4121_);
                    leanh::lean_ctor_set(v___x_4122_, 1, v_suffix_4075_);
                    v___x_4123_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4122_, v___y_4103_, v___y_4104_);
                    return v___x_4123_;
                }
                2 => match v___y_4102_ {
                    1 => {
                        leanh::lean_dec_ref(v_suffix_4075_);
                        leanh::lean_dec(v_declName_4073_);
                        state = 5;
                        continue;
                    }
                    3 => {
                        leanh::lean_dec_ref(v_suffix_4075_);
                        leanh::lean_dec(v_declName_4073_);
                        state = 5;
                        continue;
                    }
                    _ => {
                        if v___x_4100_ == 0 {
                            v___x_4124_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9);
                            v___x_4125_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4126_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4126_, 0, v___x_4124_);
                            leanh::lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                            v___x_4127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11);
                            v___x_4128_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                            leanh::lean_ctor_set(v___x_4128_, 1, v___x_4127_);
                            v___x_4129_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
                            v___x_4131_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4131_, 0, v___x_4128_);
                            leanh::lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                            v___x_4132_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4133_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4133_, 0, v___x_4131_);
                            leanh::lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                            v___x_4134_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4134_, 0, v___x_4133_);
                            leanh::lean_ctor_set(v___x_4134_, 1, v_suffix_4075_);
                            v___x_4135_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4134_, v___y_4103_, v___y_4104_);
                            return v___x_4135_;
                        } else {
                            leanh::lean_dec_ref(v_suffix_4075_);
                            leanh::lean_dec(v_declName_4073_);
                            state = 5;
                            continue;
                        }
                    }
                },
                _ => {
                    if v___y_4102_ == 1 {
                        leanh::lean_dec_ref(v_suffix_4075_);
                        leanh::lean_dec(v_declName_4073_);
                        state = 4;
                        continue;
                    } else {
                        if v___x_4100_ == 0 {
                            v___x_4136_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13);
                            v___x_4137_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4138_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4138_, 0, v___x_4136_);
                            leanh::lean_ctor_set(v___x_4138_, 1, v___x_4137_);
                            v___x_4139_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
                            v___x_4140_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4140_, 0, v___x_4138_);
                            leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                            v___x_4141_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4142_ = l_Lean_stringToMessageData(v___x_4141_);
                            v___x_4143_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4143_, 0, v___x_4140_);
                            leanh::lean_ctor_set(v___x_4143_, 1, v___x_4142_);
                            v___x_4144_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4145_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4145_, 0, v___x_4143_);
                            leanh::lean_ctor_set(v___x_4145_, 1, v___x_4144_);
                            v___x_4146_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                            leanh::lean_ctor_set(v___x_4146_, 1, v_suffix_4075_);
                            v___x_4147_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4146_, v___y_4103_, v___y_4104_);
                            return v___x_4147_;
                        } else {
                            leanh::lean_dec_ref(v_suffix_4075_);
                            leanh::lean_dec(v_declName_4073_);
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            8 => {
                v___x_4152_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
                v___x_4153_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                v___x_4154_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4154_, 0, v___x_4152_);
                leanh::lean_ctor_set(v___x_4154_, 1, v___x_4153_);
                v___x_4155_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17);
                v___x_4156_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4156_, 0, v___x_4154_);
                leanh::lean_ctor_set(v___x_4156_, 1, v___x_4155_);
                v___x_4157_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4157_, 0, v___x_4156_);
                leanh::lean_ctor_set(v___x_4157_, 1, v_suffix_4075_);
                v___x_4158_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4157_, v___y_4151_, v___y_4149_);
                return v___x_4158_;
            }
            9 => {
                v___x_4162_ = lean_st_ref_get(v___y_4161_);
                v_env_4163_ = leanh::lean_ctor_get(v___x_4162_, 0);
                leanh::lean_inc_ref(v_env_4163_);
                leanh::lean_dec(v___x_4162_);
                leanh::lean_inc(v_declName_4073_);
                v___x_4164_ = lean_get_reducibility_status(v_env_4163_, v_declName_4073_);
                match v_attrKind_4076_ {
                    0 => {
                        v___x_4165_ = lean_st_ref_get(v___y_4161_);
                        v_env_4166_ = leanh::lean_ctor_get(v___x_4165_, 0);
                        leanh::lean_inc_ref(v_env_4166_);
                        leanh::lean_dec(v___x_4165_);
                        v___x_4167_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_4166_, v_declName_4073_);
                        leanh::lean_dec_ref(v_env_4166_);
                        if leanh::lean_obj_tag(v___x_4167_) == 1 {
                            leanh::lean_dec_ref_known(v___x_4167_, 1);
                            v___y_4149_ = v___y_4161_;
                            v___y_4150_ = v___x_4164_;
                            v___y_4151_ = v___y_4160_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4167_);
                            if v___x_4100_ == 0 {
                                v___y_4102_ = v___x_4164_;
                                v___y_4103_ = v___y_4160_;
                                v___y_4104_ = v___y_4161_;
                                state = 7;
                                continue;
                            } else {
                                v___y_4149_ = v___y_4161_;
                                v___y_4150_ = v___x_4164_;
                                v___y_4151_ = v___y_4160_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                    1 => match v_status_4074_ {
                        0 => {
                            v___x_4168_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
                            v___x_4169_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4170_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4170_, 0, v___x_4168_);
                            leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                            v___x_4171_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21);
                            v___x_4172_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4172_, 0, v___x_4170_);
                            leanh::lean_ctor_set(v___x_4172_, 1, v___x_4171_);
                            v___x_4173_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_4173_, 0, v___x_4172_);
                            leanh::lean_ctor_set(v___x_4173_, 1, v_suffix_4075_);
                            v___x_4174_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4173_, v___y_4160_, v___y_4161_);
                            return v___x_4174_;
                        }
                        1 => {
                            if v___x_4164_ == 2 {
                                leanh::lean_dec_ref(v_suffix_4075_);
                                leanh::lean_dec(v_declName_4073_);
                                state = 1;
                                continue;
                            } else {
                                if v___x_4100_ == 0 {
                                    v___x_4175_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23);
                                    v___x_4176_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4177_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4177_, 0, v___x_4175_);
                                    leanh::lean_ctor_set(v___x_4177_, 1, v___x_4176_);
                                    v___x_4178_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4179_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4179_, 0, v___x_4177_);
                                    leanh::lean_ctor_set(v___x_4179_, 1, v___x_4178_);
                                    v___x_4180_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4181_ = l_Lean_stringToMessageData(v___x_4180_);
                                    v___x_4182_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4182_, 0, v___x_4179_);
                                    leanh::lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                                    v___x_4183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27);
                                    v___x_4184_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4184_, 0, v___x_4182_);
                                    leanh::lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                                    v___x_4185_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4185_, 0, v___x_4184_);
                                    leanh::lean_ctor_set(v___x_4185_, 1, v_suffix_4075_);
                                    v___x_4186_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4185_, v___y_4160_, v___y_4161_);
                                    return v___x_4186_;
                                } else {
                                    leanh::lean_dec_ref(v_suffix_4075_);
                                    leanh::lean_dec(v_declName_4073_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        2 => match v___x_4164_ {
                            1 => {
                                leanh::lean_dec_ref(v_suffix_4075_);
                                leanh::lean_dec(v_declName_4073_);
                                state = 2;
                                continue;
                            }
                            3 => {
                                leanh::lean_dec_ref(v_suffix_4075_);
                                leanh::lean_dec(v_declName_4073_);
                                state = 2;
                                continue;
                            }
                            _ => {
                                if v___x_4100_ == 0 {
                                    v___x_4187_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
                                    v___x_4188_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4189_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4189_, 0, v___x_4187_);
                                    leanh::lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                                    v___x_4190_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4191_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4191_, 0, v___x_4189_);
                                    leanh::lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                                    v___x_4192_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4193_ = l_Lean_stringToMessageData(v___x_4192_);
                                    v___x_4194_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4194_, 0, v___x_4191_);
                                    leanh::lean_ctor_set(v___x_4194_, 1, v___x_4193_);
                                    v___x_4195_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31);
                                    v___x_4196_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4196_, 0, v___x_4194_);
                                    leanh::lean_ctor_set(v___x_4196_, 1, v___x_4195_);
                                    v___x_4197_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                                    leanh::lean_ctor_set(v___x_4197_, 1, v_suffix_4075_);
                                    v___x_4198_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4197_, v___y_4160_, v___y_4161_);
                                    return v___x_4198_;
                                } else {
                                    leanh::lean_dec_ref(v_suffix_4075_);
                                    leanh::lean_dec(v_declName_4073_);
                                    state = 2;
                                    continue;
                                }
                            }
                        },
                        _ => {
                            if v___x_4164_ == 1 {
                                leanh::lean_dec_ref(v_suffix_4075_);
                                leanh::lean_dec(v_declName_4073_);
                                state = 3;
                                continue;
                            } else {
                                if v___x_4100_ == 0 {
                                    v___x_4199_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33);
                                    v___x_4200_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4201_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4201_, 0, v___x_4199_);
                                    leanh::lean_ctor_set(v___x_4201_, 1, v___x_4200_);
                                    v___x_4202_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4203_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4203_, 0, v___x_4201_);
                                    leanh::lean_ctor_set(v___x_4203_, 1, v___x_4202_);
                                    v___x_4204_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4205_ = l_Lean_stringToMessageData(v___x_4204_);
                                    v___x_4206_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4206_, 0, v___x_4203_);
                                    leanh::lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                                    v___x_4207_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35);
                                    v___x_4208_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4208_, 0, v___x_4206_);
                                    leanh::lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                                    v___x_4209_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_4209_, 0, v___x_4208_);
                                    leanh::lean_ctor_set(v___x_4209_, 1, v_suffix_4075_);
                                    v___x_4210_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4209_, v___y_4160_, v___y_4161_);
                                    return v___x_4210_;
                                } else {
                                    leanh::lean_dec_ref(v_suffix_4075_);
                                    leanh::lean_dec(v_declName_4073_);
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    },
                    _ => {
                        v___x_4211_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37);
                        v___x_4212_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                        v___x_4213_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4213_, 0, v___x_4211_);
                        leanh::lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                        v___x_4214_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39);
                        v___x_4215_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4215_, 0, v___x_4213_);
                        leanh::lean_ctor_set(v___x_4215_, 1, v___x_4214_);
                        v___x_4216_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4216_, 0, v___x_4215_);
                        leanh::lean_ctor_set(v___x_4216_, 1, v_suffix_4075_);
                        v___x_4217_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4216_, v___y_4160_, v___y_4161_);
                        return v___x_4217_;
                    }
                }
            }
            10 => {
                if v_isShared_4231_ == 0 {
                    v___x_4233_ = v___x_4230_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4234_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
                    v___x_4233_ = v_reuseFailAlloc_4234_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed(
    mut v_declName_4238_: *mut leanh::LeanObject,
    mut v_status_4239_: *mut leanh::LeanObject,
    mut v_suffix_4240_: *mut leanh::LeanObject,
    mut v_attrKind_4241_: *mut leanh::LeanObject,
    mut v___y_4242_: *mut leanh::LeanObject,
    mut v___y_4243_: *mut leanh::LeanObject,
    mut v___y_4244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_boxed_4245_: u8 = 0;
    let mut v_attrKind_boxed_4246_: u8 = 0;
    let mut v_res_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_boxed_4245_ = (leanh::lean_unbox(v_status_4239_) as u8);
    v_attrKind_boxed_4246_ = (leanh::lean_unbox(v_attrKind_4241_) as u8);
    v_res_4247_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(
        v_declName_4238_,
        v_status_boxed_4245_,
        v_suffix_4240_,
        v_attrKind_boxed_4246_,
        v___y_4242_,
        v___y_4243_,
    );
    leanh::lean_dec(v___y_4243_);
    leanh::lean_dec_ref(v___y_4242_);
    return v_res_4247_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(
    mut v___y_4248_: *mut leanh::LeanObject,
    mut v_isExporting_4249_: u8,
    mut v___x_4250_: *mut leanh::LeanObject,
    mut v_a_x3f_4251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4253_ = lean_st_ref_take(v___y_4248_);
                v_env_4254_ = leanh::lean_ctor_get(v___x_4253_, 0);
                v_nextMacroScope_4255_ = leanh::lean_ctor_get(v___x_4253_, 1);
                v_ngen_4256_ = leanh::lean_ctor_get(v___x_4253_, 2);
                v_auxDeclNGen_4257_ = leanh::lean_ctor_get(v___x_4253_, 3);
                v_traceState_4258_ = leanh::lean_ctor_get(v___x_4253_, 4);
                v_messages_4259_ = leanh::lean_ctor_get(v___x_4253_, 6);
                v_infoState_4260_ = leanh::lean_ctor_get(v___x_4253_, 7);
                v_snapshotTasks_4261_ = leanh::lean_ctor_get(v___x_4253_, 8);
                v_isSharedCheck_4272_ = (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v_unused_4273_ = leanh::lean_ctor_get(v___x_4253_, 5);
                    leanh::lean_dec(v_unused_4273_);
                    v___x_4263_ = v___x_4253_;
                    v_isShared_4264_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4261_);
                    leanh::lean_inc(v_infoState_4260_);
                    leanh::lean_inc(v_messages_4259_);
                    leanh::lean_inc(v_traceState_4258_);
                    leanh::lean_inc(v_auxDeclNGen_4257_);
                    leanh::lean_inc(v_ngen_4256_);
                    leanh::lean_inc(v_nextMacroScope_4255_);
                    leanh::lean_inc(v_env_4254_);
                    leanh::lean_dec(v___x_4253_);
                    v___x_4263_ = leanh::lean_box(0);
                    v_isShared_4264_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4265_ = l_Lean_Environment_setExporting(v_env_4254_, v_isExporting_4249_);
                if v_isShared_4264_ == 0 {
                    leanh::lean_ctor_set(v___x_4263_, 5, v___x_4250_);
                    leanh::lean_ctor_set(v___x_4263_, 0, v___x_4265_);
                    v___x_4267_ = v___x_4263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_nextMacroScope_4255_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_ngen_4256_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_auxDeclNGen_4257_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_traceState_4258_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 5, v___x_4250_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 6, v_messages_4259_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 7, v_infoState_4260_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 8, v_snapshotTasks_4261_);
                    v___x_4267_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4268_ = lean_st_ref_set(v___y_4248_, v___x_4267_);
                v___x_4269_ = leanh::lean_box(0);
                v___x_4270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4270_, 0, v___x_4269_);
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(
    mut v___y_4274_: *mut leanh::LeanObject,
    mut v_isExporting_4275_: *mut leanh::LeanObject,
    mut v___x_4276_: *mut leanh::LeanObject,
    mut v_a_x3f_4277_: *mut leanh::LeanObject,
    mut v___y_4278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4279_: u8 = 0;
    let mut v_res_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4279_ = (leanh::lean_unbox(v_isExporting_4275_) as u8);
    v_res_4280_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4274_, v_isExporting_boxed_4279_, v___x_4276_, v_a_x3f_4277_);
    leanh::lean_dec(v_a_x3f_4277_);
    leanh::lean_dec(v___y_4274_);
    return v_res_4280_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4281_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0);
    v___x_4283_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4283_, 0, v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4284_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
    v___x_4285_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4285_, 0, v___x_4284_);
    leanh::lean_ctor_set(v___x_4285_, 1, v___x_4284_);
    return v___x_4285_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(
    mut v_x_4286_: *mut leanh::LeanObject,
    mut v_isExporting_4287_: u8,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4293_: u8 = 0;
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4325_: u8 = 0;
    let mut v_unused_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_unused_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_unused_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4291_ = lean_st_ref_get(v___y_4289_);
                v_env_4292_ = leanh::lean_ctor_get(v___x_4291_, 0);
                leanh::lean_inc_ref(v_env_4292_);
                leanh::lean_dec(v___x_4291_);
                v_isExporting_4293_ = leanh::lean_ctor_get_uint8(
                    v_env_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_4292_);
                v___x_4294_ = lean_st_ref_take(v___y_4289_);
                v_env_4295_ = leanh::lean_ctor_get(v___x_4294_, 0);
                v_nextMacroScope_4296_ = leanh::lean_ctor_get(v___x_4294_, 1);
                v_ngen_4297_ = leanh::lean_ctor_get(v___x_4294_, 2);
                v_auxDeclNGen_4298_ = leanh::lean_ctor_get(v___x_4294_, 3);
                v_traceState_4299_ = leanh::lean_ctor_get(v___x_4294_, 4);
                v_messages_4300_ = leanh::lean_ctor_get(v___x_4294_, 6);
                v_infoState_4301_ = leanh::lean_ctor_get(v___x_4294_, 7);
                v_snapshotTasks_4302_ = leanh::lean_ctor_get(v___x_4294_, 8);
                v_isSharedCheck_4341_ = (!leanh::lean_is_exclusive(v___x_4294_)) as u8;
                if v_isSharedCheck_4341_ == 0 {
                    v_unused_4342_ = leanh::lean_ctor_get(v___x_4294_, 5);
                    leanh::lean_dec(v_unused_4342_);
                    v___x_4304_ = v___x_4294_;
                    v_isShared_4305_ = v_isSharedCheck_4341_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4302_);
                    leanh::lean_inc(v_infoState_4301_);
                    leanh::lean_inc(v_messages_4300_);
                    leanh::lean_inc(v_traceState_4299_);
                    leanh::lean_inc(v_auxDeclNGen_4298_);
                    leanh::lean_inc(v_ngen_4297_);
                    leanh::lean_inc(v_nextMacroScope_4296_);
                    leanh::lean_inc(v_env_4295_);
                    leanh::lean_dec(v___x_4294_);
                    v___x_4304_ = leanh::lean_box(0);
                    v_isShared_4305_ = v_isSharedCheck_4341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4306_ = l_Lean_Environment_setExporting(v_env_4295_, v_isExporting_4287_);
                v___x_4307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
                if v_isShared_4305_ == 0 {
                    leanh::lean_ctor_set(v___x_4304_, 5, v___x_4307_);
                    leanh::lean_ctor_set(v___x_4304_, 0, v___x_4306_);
                    v___x_4309_ = v___x_4304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_nextMacroScope_4296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_ngen_4297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_auxDeclNGen_4298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_traceState_4299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 5, v___x_4307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 6, v_messages_4300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 7, v_infoState_4301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 8, v_snapshotTasks_4302_);
                    v___x_4309_ = v_reuseFailAlloc_4340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4310_ = lean_st_ref_set(v___y_4289_, v___x_4309_);
                leanh::lean_inc(v___y_4289_);
                leanh::lean_inc_ref(v___y_4288_);
                v_r_4311_ = leanh::lean_apply_3(
                    v_x_4286_,
                    v___y_4288_,
                    v___y_4289_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v_r_4311_) == 0 {
                    v_a_4312_ = leanh::lean_ctor_get(v_r_4311_, 0);
                    v_isSharedCheck_4328_ = (!leanh::lean_is_exclusive(v_r_4311_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4314_ = v_r_4311_;
                        v_isShared_4315_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4312_);
                        leanh::lean_dec(v_r_4311_);
                        v___x_4314_ = leanh::lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4329_ = leanh::lean_ctor_get(v_r_4311_, 0);
                    leanh::lean_inc(v_a_4329_);
                    leanh::lean_dec_ref_known(v_r_4311_, 1);
                    v___x_4330_ = leanh::lean_box(0);
                    v___x_4331_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4289_, v_isExporting_4293_, v___x_4307_, v___x_4330_);
                    v_isSharedCheck_4338_ = (!leanh::lean_is_exclusive(v___x_4331_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v_unused_4339_ = leanh::lean_ctor_get(v___x_4331_, 0);
                        leanh::lean_dec(v_unused_4339_);
                        v___x_4333_ = v___x_4331_;
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_4331_);
                        v___x_4333_ = leanh::lean_box(0);
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v_a_4312_);
                if v_isShared_4315_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4314_, 1);
                    v___x_4317_ = v___x_4314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4312_);
                    v___x_4317_ = v_reuseFailAlloc_4327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4318_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4289_, v_isExporting_4293_, v___x_4307_, v___x_4317_);
                leanh::lean_dec_ref(v___x_4317_);
                v_isSharedCheck_4325_ = (!leanh::lean_is_exclusive(v___x_4318_)) as u8;
                if v_isSharedCheck_4325_ == 0 {
                    v_unused_4326_ = leanh::lean_ctor_get(v___x_4318_, 0);
                    leanh::lean_dec(v_unused_4326_);
                    v___x_4320_ = v___x_4318_;
                    v_isShared_4321_ = v_isSharedCheck_4325_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_dec(v___x_4318_);
                    v___x_4320_ = leanh::lean_box(0);
                    v_isShared_4321_ = v_isSharedCheck_4325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4321_ == 0 {
                    leanh::lean_ctor_set(v___x_4320_, 0, v_a_4312_);
                    v___x_4323_ = v___x_4320_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4312_);
                    v___x_4323_ = v_reuseFailAlloc_4324_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4323_;
            }
            7 => {
                if v_isShared_4334_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4333_, 1);
                    leanh::lean_ctor_set(v___x_4333_, 0, v_a_4329_);
                    v___x_4336_ = v___x_4333_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4329_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___boxed(
    mut v_x_4343_: *mut leanh::LeanObject,
    mut v_isExporting_4344_: *mut leanh::LeanObject,
    mut v___y_4345_: *mut leanh::LeanObject,
    mut v___y_4346_: *mut leanh::LeanObject,
    mut v___y_4347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4348_: u8 = 0;
    let mut v_res_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4348_ = (leanh::lean_unbox(v_isExporting_4344_) as u8);
    v_res_4349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4343_, v_isExporting_boxed_4348_, v___y_4345_, v___y_4346_);
    leanh::lean_dec(v___y_4346_);
    leanh::lean_dec_ref(v___y_4345_);
    return v_res_4349_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(
    mut v_x_4350_: *mut leanh::LeanObject,
    mut v_when_4351_: u8,
    mut v___y_4352_: *mut leanh::LeanObject,
    mut v___y_4353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_when_4351_ == 0 {
        let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_4353_);
        leanh::lean_inc_ref(v___y_4352_);
        v___x_4355_ = leanh::lean_apply_3(
            v_x_4350_,
            v___y_4352_,
            v___y_4353_,
            leanh::lean_box(0),
        );
        return v___x_4355_;
    } else {
        let mut v___x_4356_: u8 = 0;
        let mut v___x_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4356_ = 0;
        v___x_4357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4350_, v___x_4356_, v___y_4352_, v___y_4353_);
        return v___x_4357_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(
    mut v_x_4358_: *mut leanh::LeanObject,
    mut v_when_4359_: *mut leanh::LeanObject,
    mut v___y_4360_: *mut leanh::LeanObject,
    mut v___y_4361_: *mut leanh::LeanObject,
    mut v___y_4362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4363_: u8 = 0;
    let mut v_res_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4363_ = (leanh::lean_unbox(v_when_4359_) as u8);
    v_res_4364_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_4358_, v_when_boxed_4363_, v___y_4360_, v___y_4361_);
    leanh::lean_dec(v___y_4361_);
    leanh::lean_dec_ref(v___y_4360_);
    return v_res_4364_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4368_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1;
    v___x_4369_ = l_Lean_MessageData_ofFormat(v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suffix_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4370_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2),
        core::ptr::addr_of_mut!(
            l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once
        ),
        _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2,
    );
    v_suffix_4371_ = l_Lean_MessageData_note(v___x_4370_);
    return v_suffix_4371_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate(
    mut v_declName_4372_: *mut leanh::LeanObject,
    mut v_status_4373_: u8,
    mut v_attrKind_4374_: u8,
    mut v_a_4375_: *mut leanh::LeanObject,
    mut v_a_4376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_suffix_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_suffix_4378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once
        ),
        _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3,
    );
    v___x_4379_ = leanh::lean_box((v_status_4373_) as usize);
    v___x_4380_ = leanh::lean_box((v_attrKind_4374_) as usize);
    v___f_4381_ = leanh::lean_alloc_closure(
        l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        4,
    );
    leanh::lean_closure_set(v___f_4381_, 0, v_declName_4372_);
    leanh::lean_closure_set(v___f_4381_, 1, v___x_4379_);
    leanh::lean_closure_set(v___f_4381_, 2, v_suffix_4378_);
    leanh::lean_closure_set(v___f_4381_, 3, v___x_4380_);
    v___x_4382_ = 1;
    v___x_4383_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v___f_4381_, v___x_4382_, v_a_4375_, v_a_4376_);
    return v___x_4383_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(
    mut v_declName_4384_: *mut leanh::LeanObject,
    mut v_status_4385_: *mut leanh::LeanObject,
    mut v_attrKind_4386_: *mut leanh::LeanObject,
    mut v_a_4387_: *mut leanh::LeanObject,
    mut v_a_4388_: *mut leanh::LeanObject,
    mut v_a_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_boxed_4390_: u8 = 0;
    let mut v_attrKind_boxed_4391_: u8 = 0;
    let mut v_res_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_boxed_4390_ = (leanh::lean_unbox(v_status_4385_) as u8);
    v_attrKind_boxed_4391_ = (leanh::lean_unbox(v_attrKind_4386_) as u8);
    v_res_4392_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(
        v_declName_4384_,
        v_status_boxed_4390_,
        v_attrKind_boxed_4391_,
        v_a_4387_,
        v_a_4388_,
    );
    leanh::lean_dec(v_a_4388_);
    leanh::lean_dec_ref(v_a_4387_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(
    mut v_00_u03b1_4393_: *mut leanh::LeanObject,
    mut v_msg_4394_: *mut leanh::LeanObject,
    mut v___y_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_4394_, v___y_4395_, v___y_4396_);
    return v___x_4398_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(
    mut v_00_u03b1_4399_: *mut leanh::LeanObject,
    mut v_msg_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
    mut v___y_4403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4404_ =
        l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(
            v_00_u03b1_4399_,
            v_msg_4400_,
            v___y_4401_,
            v___y_4402_,
        );
    leanh::lean_dec(v___y_4402_);
    leanh::lean_dec_ref(v___y_4401_);
    return v_res_4404_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(
    mut v_00_u03b1_4405_: *mut leanh::LeanObject,
    mut v_x_4406_: *mut leanh::LeanObject,
    mut v_isExporting_4407_: u8,
    mut v___y_4408_: *mut leanh::LeanObject,
    mut v___y_4409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4406_, v_isExporting_4407_, v___y_4408_, v___y_4409_);
    return v___x_4411_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(
    mut v_00_u03b1_4412_: *mut leanh::LeanObject,
    mut v_x_4413_: *mut leanh::LeanObject,
    mut v_isExporting_4414_: *mut leanh::LeanObject,
    mut v___y_4415_: *mut leanh::LeanObject,
    mut v___y_4416_: *mut leanh::LeanObject,
    mut v___y_4417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isExporting_boxed_4418_: u8 = 0;
    let mut v_res_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4418_ = (leanh::lean_unbox(v_isExporting_4414_) as u8);
    v_res_4419_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(v_00_u03b1_4412_, v_x_4413_, v_isExporting_boxed_4418_, v___y_4415_, v___y_4416_);
    leanh::lean_dec(v___y_4416_);
    leanh::lean_dec_ref(v___y_4415_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(
    mut v_00_u03b1_4420_: *mut leanh::LeanObject,
    mut v_x_4421_: *mut leanh::LeanObject,
    mut v_when_4422_: u8,
    mut v___y_4423_: *mut leanh::LeanObject,
    mut v___y_4424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4426_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_4421_, v_when_4422_, v___y_4423_, v___y_4424_);
    return v___x_4426_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(
    mut v_00_u03b1_4427_: *mut leanh::LeanObject,
    mut v_x_4428_: *mut leanh::LeanObject,
    mut v_when_4429_: *mut leanh::LeanObject,
    mut v___y_4430_: *mut leanh::LeanObject,
    mut v___y_4431_: *mut leanh::LeanObject,
    mut v___y_4432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_when_boxed_4433_: u8 = 0;
    let mut v_res_4434_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4433_ = (leanh::lean_unbox(v_when_4429_) as u8);
    v_res_4434_ =
        l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(
            v_00_u03b1_4427_,
            v_x_4428_,
            v_when_boxed_4433_,
            v___y_4430_,
            v___y_4431_,
        );
    leanh::lean_dec(v___y_4431_);
    leanh::lean_dec_ref(v___y_4430_);
    return v_res_4434_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(
    mut v_00_u03b1_4435_: *mut leanh::LeanObject,
    mut v_constName_4436_: *mut leanh::LeanObject,
    mut v___y_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4440_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_4436_, v___y_4437_, v___y_4438_);
    return v___x_4440_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(
    mut v_00_u03b1_4441_: *mut leanh::LeanObject,
    mut v_constName_4442_: *mut leanh::LeanObject,
    mut v___y_4443_: *mut leanh::LeanObject,
    mut v___y_4444_: *mut leanh::LeanObject,
    mut v___y_4445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(v_00_u03b1_4441_, v_constName_4442_, v___y_4443_, v___y_4444_);
    leanh::lean_dec(v___y_4444_);
    leanh::lean_dec_ref(v___y_4443_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(
    mut v_00_u03b1_4447_: *mut leanh::LeanObject,
    mut v_ref_4448_: *mut leanh::LeanObject,
    mut v_constName_4449_: *mut leanh::LeanObject,
    mut v___y_4450_: *mut leanh::LeanObject,
    mut v___y_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4453_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_4448_, v_constName_4449_, v___y_4450_, v___y_4451_);
    return v___x_4453_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_4454_: *mut leanh::LeanObject,
    mut v_ref_4455_: *mut leanh::LeanObject,
    mut v_constName_4456_: *mut leanh::LeanObject,
    mut v___y_4457_: *mut leanh::LeanObject,
    mut v___y_4458_: *mut leanh::LeanObject,
    mut v___y_4459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(v_00_u03b1_4454_, v_ref_4455_, v_constName_4456_, v___y_4457_, v___y_4458_);
    leanh::lean_dec(v___y_4458_);
    leanh::lean_dec_ref(v___y_4457_);
    leanh::lean_dec(v_ref_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(
    mut v_00_u03b1_4461_: *mut leanh::LeanObject,
    mut v_ref_4462_: *mut leanh::LeanObject,
    mut v_msg_4463_: *mut leanh::LeanObject,
    mut v_declHint_4464_: *mut leanh::LeanObject,
    mut v___y_4465_: *mut leanh::LeanObject,
    mut v___y_4466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_4462_, v_msg_4463_, v_declHint_4464_, v___y_4465_, v___y_4466_);
    return v___x_4468_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b1_4469_: *mut leanh::LeanObject,
    mut v_ref_4470_: *mut leanh::LeanObject,
    mut v_msg_4471_: *mut leanh::LeanObject,
    mut v_declHint_4472_: *mut leanh::LeanObject,
    mut v___y_4473_: *mut leanh::LeanObject,
    mut v___y_4474_: *mut leanh::LeanObject,
    mut v___y_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(v_00_u03b1_4469_, v_ref_4470_, v_msg_4471_, v_declHint_4472_, v___y_4473_, v___y_4474_);
    leanh::lean_dec(v___y_4474_);
    leanh::lean_dec_ref(v___y_4473_);
    leanh::lean_dec(v_ref_4470_);
    return v_res_4476_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(
    mut v_msg_4477_: *mut leanh::LeanObject,
    mut v_declHint_4478_: *mut leanh::LeanObject,
    mut v___y_4479_: *mut leanh::LeanObject,
    mut v___y_4480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_4477_, v_declHint_4478_, v___y_4480_);
    return v___x_4482_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(
    mut v_msg_4483_: *mut leanh::LeanObject,
    mut v_declHint_4484_: *mut leanh::LeanObject,
    mut v___y_4485_: *mut leanh::LeanObject,
    mut v___y_4486_: *mut leanh::LeanObject,
    mut v___y_4487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4488_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_4483_, v_declHint_4484_, v___y_4485_, v___y_4486_);
    leanh::lean_dec(v___y_4486_);
    leanh::lean_dec_ref(v___y_4485_);
    return v_res_4488_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(
    mut v_00_u03b1_4489_: *mut leanh::LeanObject,
    mut v_ref_4490_: *mut leanh::LeanObject,
    mut v_msg_4491_: *mut leanh::LeanObject,
    mut v___y_4492_: *mut leanh::LeanObject,
    mut v___y_4493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_4490_, v_msg_4491_, v___y_4492_, v___y_4493_);
    return v___x_4495_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(
    mut v_00_u03b1_4496_: *mut leanh::LeanObject,
    mut v_ref_4497_: *mut leanh::LeanObject,
    mut v_msg_4498_: *mut leanh::LeanObject,
    mut v___y_4499_: *mut leanh::LeanObject,
    mut v___y_4500_: *mut leanh::LeanObject,
    mut v___y_4501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_4496_, v_ref_4497_, v_msg_4498_, v___y_4499_, v___y_4500_);
    leanh::lean_dec(v___y_4500_);
    leanh::lean_dec_ref(v___y_4499_);
    leanh::lean_dec(v_ref_4497_);
    return v_res_4502_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(
    mut v_status_4503_: u8,
    mut v_declName_4504_: *mut leanh::LeanObject,
    mut v_stx_4505_: *mut leanh::LeanObject,
    mut v_attrKind_4506_: u8,
    mut v_a_4507_: *mut leanh::LeanObject,
    mut v_a_4508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_unused_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_unused_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4510_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_4505_, v_a_4507_, v_a_4508_);
                if leanh::lean_obj_tag(v___x_4510_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4510_, 1);
                    leanh::lean_inc(v_declName_4504_);
                    v___x_4511_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(
                        v_declName_4504_,
                        v_status_4503_,
                        v_attrKind_4506_,
                        v_a_4507_,
                        v_a_4508_,
                    );
                    if leanh::lean_obj_tag(v___x_4511_) == 0 {
                        v_isSharedCheck_4540_ =
                            (!leanh::lean_is_exclusive(v___x_4511_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v_unused_4541_ = leanh::lean_ctor_get(v___x_4511_, 0);
                            leanh::lean_dec(v_unused_4541_);
                            v___x_4513_ = v___x_4511_;
                            v_isShared_4514_ = v_isSharedCheck_4540_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_4511_);
                            v___x_4513_ = leanh::lean_box(0);
                            v_isShared_4514_ = v_isSharedCheck_4540_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_4504_);
                        return v___x_4511_;
                    }
                } else {
                    leanh::lean_dec(v_declName_4504_);
                    return v___x_4510_;
                }
            }
            1 => {
                v___x_4515_ = lean_st_ref_take(v_a_4508_);
                v_currNamespace_4516_ = leanh::lean_ctor_get(v_a_4507_, 6);
                v_env_4517_ = leanh::lean_ctor_get(v___x_4515_, 0);
                v_nextMacroScope_4518_ = leanh::lean_ctor_get(v___x_4515_, 1);
                v_ngen_4519_ = leanh::lean_ctor_get(v___x_4515_, 2);
                v_auxDeclNGen_4520_ = leanh::lean_ctor_get(v___x_4515_, 3);
                v_traceState_4521_ = leanh::lean_ctor_get(v___x_4515_, 4);
                v_messages_4522_ = leanh::lean_ctor_get(v___x_4515_, 6);
                v_infoState_4523_ = leanh::lean_ctor_get(v___x_4515_, 7);
                v_snapshotTasks_4524_ = leanh::lean_ctor_get(v___x_4515_, 8);
                v_isSharedCheck_4538_ = (!leanh::lean_is_exclusive(v___x_4515_)) as u8;
                if v_isSharedCheck_4538_ == 0 {
                    v_unused_4539_ = leanh::lean_ctor_get(v___x_4515_, 5);
                    leanh::lean_dec(v_unused_4539_);
                    v___x_4526_ = v___x_4515_;
                    v_isShared_4527_ = v_isSharedCheck_4538_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4524_);
                    leanh::lean_inc(v_infoState_4523_);
                    leanh::lean_inc(v_messages_4522_);
                    leanh::lean_inc(v_traceState_4521_);
                    leanh::lean_inc(v_auxDeclNGen_4520_);
                    leanh::lean_inc(v_ngen_4519_);
                    leanh::lean_inc(v_nextMacroScope_4518_);
                    leanh::lean_inc(v_env_4517_);
                    leanh::lean_dec(v___x_4515_);
                    v___x_4526_ = leanh::lean_box(0);
                    v_isShared_4527_ = v_isSharedCheck_4538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_currNamespace_4516_);
                v___x_4528_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_4517_,
                    v_declName_4504_,
                    v_status_4503_,
                    v_attrKind_4506_,
                    v_currNamespace_4516_,
                );
                v___x_4529_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
                if v_isShared_4527_ == 0 {
                    leanh::lean_ctor_set(v___x_4526_, 5, v___x_4529_);
                    leanh::lean_ctor_set(v___x_4526_, 0, v___x_4528_);
                    v___x_4531_ = v___x_4526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_nextMacroScope_4518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_ngen_4519_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 3, v_auxDeclNGen_4520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 4, v_traceState_4521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 5, v___x_4529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 6, v_messages_4522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 7, v_infoState_4523_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 8, v_snapshotTasks_4524_);
                    v___x_4531_ = v_reuseFailAlloc_4537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4532_ = lean_st_ref_set(v_a_4508_, v___x_4531_);
                v___x_4533_ = leanh::lean_box(0);
                if v_isShared_4514_ == 0 {
                    leanh::lean_ctor_set(v___x_4513_, 0, v___x_4533_);
                    v___x_4535_ = v___x_4513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4535_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed(
    mut v_status_4542_: *mut leanh::LeanObject,
    mut v_declName_4543_: *mut leanh::LeanObject,
    mut v_stx_4544_: *mut leanh::LeanObject,
    mut v_attrKind_4545_: *mut leanh::LeanObject,
    mut v_a_4546_: *mut leanh::LeanObject,
    mut v_a_4547_: *mut leanh::LeanObject,
    mut v_a_4548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_status_boxed_4549_: u8 = 0;
    let mut v_attrKind_boxed_4550_: u8 = 0;
    let mut v_res_4551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_status_boxed_4549_ = (leanh::lean_unbox(v_status_4542_) as u8);
    v_attrKind_boxed_4550_ = (leanh::lean_unbox(v_attrKind_4545_) as u8);
    v_res_4551_ = l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(
        v_status_boxed_4549_,
        v_declName_4543_,
        v_stx_4544_,
        v_attrKind_boxed_4550_,
        v_a_4546_,
        v_a_4547_,
    );
    leanh::lean_dec(v_a_4547_);
    leanh::lean_dec_ref(v_a_4546_);
    return v_res_4551_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4554_ = l_Lean_stringToMessageData(v___x_4553_);
    return v___x_4554_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4556_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4557_ = l_Lean_stringToMessageData(v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(
    mut v___x_4558_: *mut leanh::LeanObject,
    mut v_decl_4559_: *mut leanh::LeanObject,
    mut v___y_4560_: *mut leanh::LeanObject,
    mut v___y_4561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4563_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
    v___x_4564_ = l_Lean_MessageData_ofName(v___x_4558_);
    v___x_4565_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4565_, 0, v___x_4563_);
    leanh::lean_ctor_set(v___x_4565_, 1, v___x_4564_);
    v___x_4566_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
    v___x_4567_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4567_, 0, v___x_4565_);
    leanh::lean_ctor_set(v___x_4567_, 1, v___x_4566_);
    v___x_4568_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4567_, v___y_4560_, v___y_4561_);
    return v___x_4568_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(
    mut v___x_4569_: *mut leanh::LeanObject,
    mut v_decl_4570_: *mut leanh::LeanObject,
    mut v___y_4571_: *mut leanh::LeanObject,
    mut v___y_4572_: *mut leanh::LeanObject,
    mut v___y_4573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4574_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(v___x_4569_, v_decl_4570_, v___y_4571_, v___y_4572_);
    leanh::lean_dec(v___y_4572_);
    leanh::lean_dec_ref(v___y_4571_);
    leanh::lean_dec(v_decl_4570_);
    return v_res_4574_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4639_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4640_ = l_Lean_registerBuiltinAttribute(v___x_4639_);
    return v___x_4640_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(
    mut v_a_4641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4642_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
    return v_res_4642_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4643_ = leanh::lean_unsigned_to_nat(4118757939);
    v___x_4644_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4645_ = l_Lean_Name_num___override(v___x_4644_, v___x_4643_);
    return v___x_4645_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4646_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4647_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4648_ = l_Lean_Name_str___override(v___x_4647_, v___x_4646_);
    return v___x_4648_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4649_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4650_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4651_ = l_Lean_Name_str___override(v___x_4650_, v___x_4649_);
    return v___x_4651_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4652_ = leanh::lean_unsigned_to_nat(2);
    v___x_4653_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4654_ = l_Lean_Name_num___override(v___x_4653_, v___x_4652_);
    return v___x_4654_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4661_ = 0;
    v___x_4662_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4663_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4665_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_4665_, 0, v___x_4664_);
    leanh::lean_ctor_set(v___x_4665_, 1, v___x_4663_);
    leanh::lean_ctor_set(v___x_4665_, 2, v___x_4662_);
    leanh::lean_ctor_set_uint8(
        v___x_4665_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4661_,
    );
    return v___x_4665_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4669_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4670_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4672_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4672_, 0, v___x_4671_);
    leanh::lean_ctor_set(v___x_4672_, 1, v___x_4670_);
    leanh::lean_ctor_set(v___x_4672_, 2, v___f_4669_);
    return v___x_4672_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4675_ = l_Lean_registerBuiltinAttribute(v___x_4674_);
    return v___x_4675_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(
    mut v_a_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4677_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
    return v_res_4677_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4678_ = leanh::lean_unsigned_to_nat(2994861043);
    v___x_4679_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4680_ = l_Lean_Name_num___override(v___x_4679_, v___x_4678_);
    return v___x_4680_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4681_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4682_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4683_ = l_Lean_Name_str___override(v___x_4682_, v___x_4681_);
    return v___x_4683_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4686_ = l_Lean_Name_str___override(v___x_4685_, v___x_4684_);
    return v___x_4686_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4687_ = leanh::lean_unsigned_to_nat(2);
    v___x_4688_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4689_ = l_Lean_Name_num___override(v___x_4688_, v___x_4687_);
    return v___x_4689_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4696_ = 0;
    v___x_4697_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4698_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4699_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4700_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_4700_, 0, v___x_4699_);
    leanh::lean_ctor_set(v___x_4700_, 1, v___x_4698_);
    leanh::lean_ctor_set(v___x_4700_, 2, v___x_4697_);
    leanh::lean_ctor_set_uint8(
        v___x_4700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_4696_,
    );
    return v___x_4700_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4704_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4705_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4706_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4707_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4707_, 0, v___x_4706_);
    leanh::lean_ctor_set(v___x_4707_, 1, v___x_4705_);
    leanh::lean_ctor_set(v___x_4707_, 2, v___f_4704_);
    return v___x_4707_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4710_ = l_Lean_registerBuiltinAttribute(v___x_4709_);
    return v___x_4710_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(
    mut v_a_4711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4712_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
    return v_res_4712_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4744_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_;
    v___x_4745_ = l_Lean_registerBuiltinAttribute(v___x_4744_);
    return v___x_4745_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2____boxed(
    mut v_a_4746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4747_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
    return v_res_4747_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4776_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_;
    v___x_4777_ = l_Lean_registerBuiltinAttribute(v___x_4776_);
    return v___x_4777_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2____boxed(
    mut v_a_4778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4779_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
    return v_res_4779_;
}
pub unsafe fn l_Lean_getReducibilityStatus___redArg___lam__0(
    mut v_declName_4780_: *mut leanh::LeanObject,
    mut v_toPure_4781_: *mut leanh::LeanObject,
    mut v_____do__lift_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4783_ = lean_get_reducibility_status(v_____do__lift_4782_, v_declName_4780_);
    v___x_4784_ = leanh::lean_box((v___x_4783_) as usize);
    v___x_4785_ =
        leanh::lean_apply_2(v_toPure_4781_, leanh::lean_box(0), v___x_4784_);
    return v___x_4785_;
}
pub unsafe fn l_Lean_getReducibilityStatus___redArg(
    mut v_inst_4786_: *mut leanh::LeanObject,
    mut v_inst_4787_: *mut leanh::LeanObject,
    mut v_declName_4788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4789_ = leanh::lean_ctor_get(v_inst_4786_, 0);
    leanh::lean_inc_ref(v_toApplicative_4789_);
    v_toBind_4790_ = leanh::lean_ctor_get(v_inst_4786_, 1);
    leanh::lean_inc(v_toBind_4790_);
    leanh::lean_dec_ref(v_inst_4786_);
    v_getEnv_4791_ = leanh::lean_ctor_get(v_inst_4787_, 0);
    leanh::lean_inc(v_getEnv_4791_);
    leanh::lean_dec_ref(v_inst_4787_);
    v_toPure_4792_ = leanh::lean_ctor_get(v_toApplicative_4789_, 1);
    leanh::lean_inc(v_toPure_4792_);
    leanh::lean_dec_ref(v_toApplicative_4789_);
    v___f_4793_ = leanh::lean_alloc_closure(
        l_Lean_getReducibilityStatus___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4793_, 0, v_declName_4788_);
    leanh::lean_closure_set(v___f_4793_, 1, v_toPure_4792_);
    v___x_4794_ = leanh::lean_apply_4(
        v_toBind_4790_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4791_,
        v___f_4793_,
    );
    return v___x_4794_;
}
pub unsafe fn l_Lean_getReducibilityStatus(
    mut v_m_4795_: *mut leanh::LeanObject,
    mut v_inst_4796_: *mut leanh::LeanObject,
    mut v_inst_4797_: *mut leanh::LeanObject,
    mut v_declName_4798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4799_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4796_, v_inst_4797_, v_declName_4798_);
    return v___x_4799_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg___lam__0(
    mut v_declName_4800_: *mut leanh::LeanObject,
    mut v_s_4801_: u8,
    mut v_env_4802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4803_: u8 = 0;
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4803_ = 0;
    v___x_4804_ = leanh::lean_box(0);
    v___x_4805_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
        v_env_4802_,
        v_declName_4800_,
        v_s_4801_,
        v___x_4803_,
        v___x_4804_,
    );
    return v___x_4805_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg___lam__0___boxed(
    mut v_declName_4806_: *mut leanh::LeanObject,
    mut v_s_4807_: *mut leanh::LeanObject,
    mut v_env_4808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4809_: u8 = 0;
    let mut v_res_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4809_ = (leanh::lean_unbox(v_s_4807_) as u8);
    v_res_4810_ = l_Lean_setReducibilityStatus___redArg___lam__0(
        v_declName_4806_,
        v_s_boxed_4809_,
        v_env_4808_,
    );
    return v_res_4810_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg(
    mut v_inst_4811_: *mut leanh::LeanObject,
    mut v_declName_4812_: *mut leanh::LeanObject,
    mut v_s_4813_: u8,
) -> *mut leanh::LeanObject {
    let mut v_modifyEnv_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyEnv_4814_ = leanh::lean_ctor_get(v_inst_4811_, 1);
    leanh::lean_inc(v_modifyEnv_4814_);
    leanh::lean_dec_ref(v_inst_4811_);
    v___x_4815_ = leanh::lean_box((v_s_4813_) as usize);
    v___f_4816_ = leanh::lean_alloc_closure(
        l_Lean_setReducibilityStatus___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4816_, 0, v_declName_4812_);
    leanh::lean_closure_set(v___f_4816_, 1, v___x_4815_);
    v___x_4817_ = leanh::lean_apply_1(v_modifyEnv_4814_, v___f_4816_);
    return v___x_4817_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg___boxed(
    mut v_inst_4818_: *mut leanh::LeanObject,
    mut v_declName_4819_: *mut leanh::LeanObject,
    mut v_s_4820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4821_: u8 = 0;
    let mut v_res_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4821_ = (leanh::lean_unbox(v_s_4820_) as u8);
    v_res_4822_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4818_, v_declName_4819_, v_s_boxed_4821_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_setReducibilityStatus(
    mut v_m_4823_: *mut leanh::LeanObject,
    mut v_inst_4824_: *mut leanh::LeanObject,
    mut v_declName_4825_: *mut leanh::LeanObject,
    mut v_s_4826_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Lean_setReducibilityStatus___redArg(v_inst_4824_, v_declName_4825_, v_s_4826_);
    return v___x_4827_;
}
pub unsafe fn l_Lean_setReducibilityStatus___boxed(
    mut v_m_4828_: *mut leanh::LeanObject,
    mut v_inst_4829_: *mut leanh::LeanObject,
    mut v_declName_4830_: *mut leanh::LeanObject,
    mut v_s_4831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_4832_: u8 = 0;
    let mut v_res_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_4832_ = (leanh::lean_unbox(v_s_4831_) as u8);
    v_res_4833_ =
        l_Lean_setReducibilityStatus(v_m_4828_, v_inst_4829_, v_declName_4830_, v_s_boxed_4832_);
    return v_res_4833_;
}
pub unsafe fn l_Lean_setReducibleAttribute___redArg(
    mut v_inst_4834_: *mut leanh::LeanObject,
    mut v_declName_4835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4836_: u8 = 0;
    let mut v___x_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4836_ = 0;
    v___x_4837_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4834_, v_declName_4835_, v___x_4836_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_setReducibleAttribute(
    mut v_m_4838_: *mut leanh::LeanObject,
    mut v_inst_4839_: *mut leanh::LeanObject,
    mut v_declName_4840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4841_ = l_Lean_setReducibleAttribute___redArg(v_inst_4839_, v_declName_4840_);
    return v___x_4841_;
}
pub unsafe fn l_Lean_isReducible___redArg___lam__0(
    mut v_toPure_4842_: *mut leanh::LeanObject,
    mut v_____do__lift_4843_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_4843_ == 0 {
        let mut v___x_4844_: u8 = 0;
        let mut v___x_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4844_ = 1;
        v___x_4845_ = leanh::lean_box((v___x_4844_) as usize);
        v___x_4846_ =
            leanh::lean_apply_2(v_toPure_4842_, leanh::lean_box(0), v___x_4845_);
        return v___x_4846_;
    } else {
        let mut v___x_4847_: u8 = 0;
        let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4847_ = 0;
        v___x_4848_ = leanh::lean_box((v___x_4847_) as usize);
        v___x_4849_ =
            leanh::lean_apply_2(v_toPure_4842_, leanh::lean_box(0), v___x_4848_);
        return v___x_4849_;
    }
}
pub unsafe fn l_Lean_isReducible___redArg___lam__0___boxed(
    mut v_toPure_4850_: *mut leanh::LeanObject,
    mut v_____do__lift_4851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_47__boxed_4852_: u8 = 0;
    let mut v_res_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_47__boxed_4852_ = (leanh::lean_unbox(v_____do__lift_4851_) as u8);
    v_res_4853_ =
        l_Lean_isReducible___redArg___lam__0(v_toPure_4850_, v_____do__lift_47__boxed_4852_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_isReducible___redArg(
    mut v_inst_4854_: *mut leanh::LeanObject,
    mut v_inst_4855_: *mut leanh::LeanObject,
    mut v_declName_4856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4857_ = leanh::lean_ctor_get(v_inst_4854_, 0);
    v_toBind_4858_ = leanh::lean_ctor_get(v_inst_4854_, 1);
    leanh::lean_inc(v_toBind_4858_);
    v_toPure_4859_ = leanh::lean_ctor_get(v_toApplicative_4857_, 1);
    leanh::lean_inc(v_toPure_4859_);
    v___x_4860_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4854_, v_inst_4855_, v_declName_4856_);
    v___f_4861_ = leanh::lean_alloc_closure(
        l_Lean_isReducible___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4861_, 0, v_toPure_4859_);
    v___x_4862_ = leanh::lean_apply_4(
        v_toBind_4858_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4860_,
        v___f_4861_,
    );
    return v___x_4862_;
}
pub unsafe fn l_Lean_isReducible(
    mut v_m_4863_: *mut leanh::LeanObject,
    mut v_inst_4864_: *mut leanh::LeanObject,
    mut v_inst_4865_: *mut leanh::LeanObject,
    mut v_declName_4866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4867_ = l_Lean_isReducible___redArg(v_inst_4864_, v_inst_4865_, v_declName_4866_);
    return v___x_4867_;
}
pub unsafe fn l_Lean_isIrreducible___redArg___lam__0(
    mut v_toPure_4868_: *mut leanh::LeanObject,
    mut v_____do__lift_4869_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_4869_ == 2 {
        let mut v___x_4870_: u8 = 0;
        let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4870_ = 1;
        v___x_4871_ = leanh::lean_box((v___x_4870_) as usize);
        v___x_4872_ =
            leanh::lean_apply_2(v_toPure_4868_, leanh::lean_box(0), v___x_4871_);
        return v___x_4872_;
    } else {
        let mut v___x_4873_: u8 = 0;
        let mut v___x_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4873_ = 0;
        v___x_4874_ = leanh::lean_box((v___x_4873_) as usize);
        v___x_4875_ =
            leanh::lean_apply_2(v_toPure_4868_, leanh::lean_box(0), v___x_4874_);
        return v___x_4875_;
    }
}
pub unsafe fn l_Lean_isIrreducible___redArg___lam__0___boxed(
    mut v_toPure_4876_: *mut leanh::LeanObject,
    mut v_____do__lift_4877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_47__boxed_4878_: u8 = 0;
    let mut v_res_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_47__boxed_4878_ = (leanh::lean_unbox(v_____do__lift_4877_) as u8);
    v_res_4879_ =
        l_Lean_isIrreducible___redArg___lam__0(v_toPure_4876_, v_____do__lift_47__boxed_4878_);
    return v_res_4879_;
}
pub unsafe fn l_Lean_isIrreducible___redArg(
    mut v_inst_4880_: *mut leanh::LeanObject,
    mut v_inst_4881_: *mut leanh::LeanObject,
    mut v_declName_4882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4883_ = leanh::lean_ctor_get(v_inst_4880_, 0);
    v_toBind_4884_ = leanh::lean_ctor_get(v_inst_4880_, 1);
    leanh::lean_inc(v_toBind_4884_);
    v_toPure_4885_ = leanh::lean_ctor_get(v_toApplicative_4883_, 1);
    leanh::lean_inc(v_toPure_4885_);
    v___x_4886_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4880_, v_inst_4881_, v_declName_4882_);
    v___f_4887_ = leanh::lean_alloc_closure(
        l_Lean_isIrreducible___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_4887_, 0, v_toPure_4885_);
    v___x_4888_ = leanh::lean_apply_4(
        v_toBind_4884_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4886_,
        v___f_4887_,
    );
    return v___x_4888_;
}
pub unsafe fn l_Lean_isIrreducible(
    mut v_m_4889_: *mut leanh::LeanObject,
    mut v_inst_4890_: *mut leanh::LeanObject,
    mut v_inst_4891_: *mut leanh::LeanObject,
    mut v_declName_4892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4893_ = l_Lean_isIrreducible___redArg(v_inst_4890_, v_inst_4891_, v_declName_4892_);
    return v___x_4893_;
}
pub unsafe fn l_Lean_isImplicitReducibleCore(
    mut v_env_4894_: *mut leanh::LeanObject,
    mut v_declName_4895_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4896_: u8 = 0;
    v___x_4896_ = lean_get_reducibility_status(v_env_4894_, v_declName_4895_);
    if v___x_4896_ == 3 {
        let mut v___x_4897_: u8 = 0;
        v___x_4897_ = 1;
        return v___x_4897_;
    } else {
        let mut v___x_4898_: u8 = 0;
        v___x_4898_ = 0;
        return v___x_4898_;
    }
}
pub unsafe fn l_Lean_isImplicitReducibleCore___boxed(
    mut v_env_4899_: *mut leanh::LeanObject,
    mut v_declName_4900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4901_: u8 = 0;
    let mut v_r_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_Lean_isImplicitReducibleCore(v_env_4899_, v_declName_4900_);
    v_r_4902_ = leanh::lean_box((v_res_4901_) as usize);
    return v_r_4902_;
}
pub unsafe fn l_Lean_isImplicitReducible___redArg___lam__0(
    mut v_declName_4903_: *mut leanh::LeanObject,
    mut v_toPure_4904_: *mut leanh::LeanObject,
    mut v_____do__lift_4905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4906_ = l_Lean_isImplicitReducibleCore(v_____do__lift_4905_, v_declName_4903_);
    v___x_4907_ = leanh::lean_box((v___x_4906_) as usize);
    v___x_4908_ =
        leanh::lean_apply_2(v_toPure_4904_, leanh::lean_box(0), v___x_4907_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_isImplicitReducible___redArg(
    mut v_inst_4909_: *mut leanh::LeanObject,
    mut v_inst_4910_: *mut leanh::LeanObject,
    mut v_declName_4911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_4912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_4913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_4912_ = leanh::lean_ctor_get(v_inst_4909_, 0);
    leanh::lean_inc_ref(v_toApplicative_4912_);
    v_toBind_4913_ = leanh::lean_ctor_get(v_inst_4909_, 1);
    leanh::lean_inc(v_toBind_4913_);
    leanh::lean_dec_ref(v_inst_4909_);
    v_getEnv_4914_ = leanh::lean_ctor_get(v_inst_4910_, 0);
    leanh::lean_inc(v_getEnv_4914_);
    leanh::lean_dec_ref(v_inst_4910_);
    v_toPure_4915_ = leanh::lean_ctor_get(v_toApplicative_4912_, 1);
    leanh::lean_inc(v_toPure_4915_);
    leanh::lean_dec_ref(v_toApplicative_4912_);
    v___f_4916_ = leanh::lean_alloc_closure(
        l_Lean_isImplicitReducible___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_4916_, 0, v_declName_4911_);
    leanh::lean_closure_set(v___f_4916_, 1, v_toPure_4915_);
    v___x_4917_ = leanh::lean_apply_4(
        v_toBind_4913_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getEnv_4914_,
        v___f_4916_,
    );
    return v___x_4917_;
}
pub unsafe fn l_Lean_isImplicitReducible(
    mut v_m_4918_: *mut leanh::LeanObject,
    mut v_inst_4919_: *mut leanh::LeanObject,
    mut v_inst_4920_: *mut leanh::LeanObject,
    mut v_declName_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lean_isImplicitReducible___redArg(v_inst_4919_, v_inst_4920_, v_declName_4921_);
    return v___x_4922_;
}
pub unsafe fn l_Lean_isInstanceReducibleCore(
    mut v_env_4923_: *mut leanh::LeanObject,
    mut v_declName_4924_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4925_: u8 = 0;
    v___x_4925_ = l_Lean_isImplicitReducibleCore(v_env_4923_, v_declName_4924_);
    return v___x_4925_;
}
pub unsafe fn l_Lean_isInstanceReducibleCore___boxed(
    mut v_env_4926_: *mut leanh::LeanObject,
    mut v_declName_4927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4928_: u8 = 0;
    let mut v_r_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_isInstanceReducibleCore(v_env_4926_, v_declName_4927_);
    v_r_4929_ = leanh::lean_box((v_res_4928_) as usize);
    return v_r_4929_;
}
pub unsafe fn l_Lean_isInstanceReducible___redArg(
    mut v_inst_4930_: *mut leanh::LeanObject,
    mut v_inst_4931_: *mut leanh::LeanObject,
    mut v_declName_4932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4933_ = l_Lean_isImplicitReducible___redArg(v_inst_4930_, v_inst_4931_, v_declName_4932_);
    return v___x_4933_;
}
pub unsafe fn l_Lean_isInstanceReducible(
    mut v_m_4934_: *mut leanh::LeanObject,
    mut v_inst_4935_: *mut leanh::LeanObject,
    mut v_inst_4936_: *mut leanh::LeanObject,
    mut v_declName_4937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4938_ = l_Lean_isImplicitReducible___redArg(v_inst_4935_, v_inst_4936_, v_declName_4937_);
    return v___x_4938_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute___redArg(
    mut v_inst_4939_: *mut leanh::LeanObject,
    mut v_declName_4940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4941_: u8 = 0;
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4941_ = 2;
    v___x_4942_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4939_, v_declName_4940_, v___x_4941_);
    return v___x_4942_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute(
    mut v_m_4943_: *mut leanh::LeanObject,
    mut v_inst_4944_: *mut leanh::LeanObject,
    mut v_declName_4945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = l_Lean_setIrreducibleAttribute___redArg(v_inst_4944_, v_declName_4945_);
    return v___x_4946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ReducibilityAttrs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedReducibilityStatus_default =
        _init_l_Lean_instInhabitedReducibilityStatus_default();
    l_Lean_instInhabitedReducibilityStatus = _init_l_Lean_instInhabitedReducibilityStatus();
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reducibilityCoreExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_reducibilityCoreExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reducibilityExtraExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_reducibilityExtraExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_allowUnsafeReducibility = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_allowUnsafeReducibility);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ReducibilityAttrs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ReducibilityAttrs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ReducibilityAttrs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ReducibilityAttrs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ReducibilityAttrs(builtin);
}