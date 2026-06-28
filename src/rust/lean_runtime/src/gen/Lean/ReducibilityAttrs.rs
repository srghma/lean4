// Lean compiler output
// Module: Lean.ReducibilityAttrs
// Imports: Lean.ScopedEnvExtension
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static mut l_Lean_instInhabitedReducibilityStatus_default: u8 = 0;
pub static mut l_Lean_instInhabitedReducibilityStatus: u8 = 0;
pub static l_Lean_instReprReducibilityStatus_repr___closed__0_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116,
            97, 116, 117, 115, 46, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__2_value: LeanStringObject<38> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116,
            97, 116, 117, 115, 46, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101,
            0,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__4_value: LeanStringObject<36> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116,
            97, 116, 117, 115, 46, 105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__6_value: LeanStringObject<42> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 42,
        m_capacity: 42,
        m_length: 41,
        m_data: [
            76, 101, 97, 110, 46, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 83, 116,
            97, 116, 117, 115, 46, 105, 109, 112, 108, 105, 99, 105, 116, 82, 101, 100, 117, 99,
            105, 98, 108, 101, 0,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_instReprReducibilityStatus_repr___closed__7_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__6_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprReducibilityStatus_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus_repr___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_instReprReducibilityStatus_repr___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__8: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprReducibilityStatus_repr___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprReducibilityStatus_repr___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprReducibilityStatus___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprReducibilityStatus_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprReducibilityStatus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprReducibilityStatus: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprReducibilityStatus___closed__0_value) as *mut LeanObject;
pub static l_Lean_instBEqReducibilityStatus___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqReducibilityStatus_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqReducibilityStatus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityStatus___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqReducibilityStatus: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqReducibilityStatus___closed__0_value) as *mut LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__0_value: LeanStringObject<12> =
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
        m_data: [91, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 0],
    };
static mut l_Lean_ReducibilityStatus_toAttrString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__1_value: LeanStringObject<16> =
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
            91, 115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 93, 0,
        ],
    };
static mut l_Lean_ReducibilityStatus_toAttrString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__2_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_ReducibilityStatus_toAttrString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_ReducibilityStatus_toAttrString___closed__3_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            91, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108,
            101, 93, 0,
        ],
    };
static mut l_Lean_ReducibilityStatus_toAttrString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ReducibilityStatus_toAttrString___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 111, 114, 101, 32, 101, 120, 116, 101, 110, 115, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 108, 111, 99, 97, 108, 32, 101, 110, 116, 114, 105, 101, 115, 58, 32, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 67, 111, 114, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,12246743371341285727 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [1 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<8> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*8 + 0) as u16, other: 8, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 69, 120, 116, 114, 97, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject,13965638932435844466 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_getReducibilityStatusCore___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getReducibilityStatusCore___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getReducibilityStatusCore___closed__0_value) as *mut LeanObject;
pub static l_Lean_getReducibilityStatusCore___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getReducibilityStatusCore___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getReducibilityStatusCore___closed__1_value) as *mut LeanObject;
static mut l_Lean_getReducibilityStatusCore___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_getReducibilityStatusCore___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [97, 108, 108, 111, 119, 85, 110, 115, 97, 102, 101, 82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,1642828907576623915 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanStringObject<235> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 235, m_capacity: 235, m_length: 234, m_data: [101, 110, 97, 98, 108, 101, 115, 32, 117, 115, 101, 114, 115, 32, 116, 111, 32, 109, 111, 100, 105, 102, 121, 32, 116, 104, 101, 32, 114, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 32, 115, 101, 116, 116, 105, 110, 103, 115, 32, 102, 111, 114, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 101, 118, 101, 110, 32, 119, 104, 101, 110, 32, 115, 117, 99, 104, 32, 99, 104, 97, 110, 103, 101, 115, 32, 97, 114, 101, 32, 100, 101, 101, 109, 101, 100, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 32, 104, 97, 122, 97, 114, 100, 111, 117, 115, 46, 32, 70, 111, 114, 32, 101, 120, 97, 109, 112, 108, 101, 44, 32, 96, 115, 105, 109, 112, 96, 32, 97, 110, 100, 32, 116, 121, 112, 101, 32, 99, 108, 97, 115, 115, 32, 114, 101, 115, 111, 108, 117, 116, 105, 111, 110, 32, 109, 97, 105, 110, 116, 97, 105, 110, 32, 116, 101, 114, 109, 32, 105, 110, 100, 105, 99, 101, 115, 32, 119, 104, 101, 114, 101, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32, 101, 120, 112, 97, 110, 100, 101, 100, 46, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,681850948520615530 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value:
    LeanStringObject<44> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value:
    LeanStringObject<38> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value:
    LeanStringObject<49> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value:
    LeanStringObject<33> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value:
    LeanStringObject<71> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value:
    LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value:
    LeanStringObject<37> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value:
    LeanStringObject<73> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value:
    LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value:
    LeanStringObject<111> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value:
    LeanStringObject<41> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value:
    LeanStringObject<17> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value:
    LeanStringObject<57> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value:
    LeanStringObject<46> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value:
    LeanStringObject<30> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value:
    LeanStringObject<40> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value:
    LeanStringObject<71> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40_value
) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value: LeanStringObject<
    89,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value: LeanCtorObject<
    1,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__0_value
    ) as *mut LeanObject],
};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [82, 101, 100, 117, 99, 105, 98, 105, 108, 105, 116, 121, 65, 116, 116, 114, 115, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,16674771574477616125 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,8591613141613872776 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,535016304756014689 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,12932279219522036888 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,1194659137222478697 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__value) as *mut LeanObject,8790433524930448172 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__11_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,12136383179595628843 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,((( 562565324 as usize) << 1) | 1) as *mut LeanObject,74207542672438541 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__13_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,5664183133159884526 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__15_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,2546798191073904962 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__17_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,12674079943837901979 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__19_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,6878064079637565245 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [105, 114, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__18_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__20_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__22_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__23_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__24_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__21_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject,7045040058828669725 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject,2616510057874194026 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,((( 448179520 as usize) << 1) | 1) as *mut LeanObject,8351696710712280576 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,6815184137236015063 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,17909152065865606463 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,9821775911497995642 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,11290700302157177994 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [105, 109, 112, 108, 105, 99, 105, 116, 32, 114, 101, 100, 117, 99, 105, 98, 108, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_addAttr___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,((( 598760241 as usize) << 1) | 1) as *mut LeanObject,13228617787602902987 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,17949311112788899376 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__value) as *mut LeanObject,10027910081678967092 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,11004149243798455437 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [105, 110, 115, 116, 97, 110, 99, 101, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,1015365147026633853 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [97, 108, 105, 97, 115, 32, 102, 111, 114, 32, 105, 109, 112, 108, 105, 99, 105, 116, 95, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,0 as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Lean_ReducibilityStatus_ctorIdx(mut v_x_2474_: u8) -> *mut LeanObject {
    match v_x_2474_ {
        0 => {
            let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
            v___x_2475_ = lean_unsigned_to_nat(0);
            return v___x_2475_;
        }
        1 => {
            let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
            v___x_2476_ = lean_unsigned_to_nat(1);
            return v___x_2476_;
        }
        2 => {
            let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
            v___x_2477_ = lean_unsigned_to_nat(2);
            return v___x_2477_;
        }
        _ => {
            let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
            v___x_2478_ = lean_unsigned_to_nat(3);
            return v___x_2478_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorIdx___boxed(
    mut v_x_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2480_: u8 = 0;
    let mut v_res_2481_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2480_ = (lean_unbox(v_x_2479_) as u8);
    v_res_2481_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_boxed_2480_);
    return v_res_2481_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toCtorIdx(mut v_x_2482_: u8) -> *mut LeanObject {
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2483_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_2482_);
    return v___x_2483_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toCtorIdx___boxed(
    mut v_x_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_2485_: u8 = 0;
    let mut v_res_2486_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_2485_ = (lean_unbox(v_x_2484_) as u8);
    v_res_2486_ = l_Lean_ReducibilityStatus_toCtorIdx(v_x_4__boxed_2485_);
    return v_res_2486_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___redArg(
    mut v_k_2487_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2487_);
    return v_k_2487_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___redArg___boxed(
    mut v_k_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2489_: *mut LeanObject = core::ptr::null_mut();
    v_res_2489_ = l_Lean_ReducibilityStatus_ctorElim___redArg(v_k_2488_);
    lean_dec(v_k_2488_);
    return v_res_2489_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim(
    mut v_motive_2490_: *mut LeanObject,
    mut v_ctorIdx_2491_: *mut LeanObject,
    mut v_t_2492_: u8,
    mut v_h_2493_: *mut LeanObject,
    mut v_k_2494_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_2494_);
    return v_k_2494_;
}
pub unsafe fn l_Lean_ReducibilityStatus_ctorElim___boxed(
    mut v_motive_2495_: *mut LeanObject,
    mut v_ctorIdx_2496_: *mut LeanObject,
    mut v_t_2497_: *mut LeanObject,
    mut v_h_2498_: *mut LeanObject,
    mut v_k_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2500_: u8 = 0;
    let mut v_res_2501_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2500_ = (lean_unbox(v_t_2497_) as u8);
    v_res_2501_ = l_Lean_ReducibilityStatus_ctorElim(
        v_motive_2495_,
        v_ctorIdx_2496_,
        v_t_boxed_2500_,
        v_h_2498_,
        v_k_2499_,
    );
    lean_dec(v_k_2499_);
    lean_dec(v_ctorIdx_2496_);
    return v_res_2501_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___redArg(
    mut v_reducible_2502_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reducible_2502_);
    return v_reducible_2502_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___redArg___boxed(
    mut v_reducible_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2504_: *mut LeanObject = core::ptr::null_mut();
    v_res_2504_ = l_Lean_ReducibilityStatus_reducible_elim___redArg(v_reducible_2503_);
    lean_dec(v_reducible_2503_);
    return v_res_2504_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim(
    mut v_motive_2505_: *mut LeanObject,
    mut v_t_2506_: u8,
    mut v_h_2507_: *mut LeanObject,
    mut v_reducible_2508_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_reducible_2508_);
    return v_reducible_2508_;
}
pub unsafe fn l_Lean_ReducibilityStatus_reducible_elim___boxed(
    mut v_motive_2509_: *mut LeanObject,
    mut v_t_2510_: *mut LeanObject,
    mut v_h_2511_: *mut LeanObject,
    mut v_reducible_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2513_: u8 = 0;
    let mut v_res_2514_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2513_ = (lean_unbox(v_t_2510_) as u8);
    v_res_2514_ = l_Lean_ReducibilityStatus_reducible_elim(
        v_motive_2509_,
        v_t_boxed_2513_,
        v_h_2511_,
        v_reducible_2512_,
    );
    lean_dec(v_reducible_2512_);
    return v_res_2514_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___redArg(
    mut v_semireducible_2515_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_semireducible_2515_);
    return v_semireducible_2515_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___redArg___boxed(
    mut v_semireducible_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2517_: *mut LeanObject = core::ptr::null_mut();
    v_res_2517_ = l_Lean_ReducibilityStatus_semireducible_elim___redArg(v_semireducible_2516_);
    lean_dec(v_semireducible_2516_);
    return v_res_2517_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim(
    mut v_motive_2518_: *mut LeanObject,
    mut v_t_2519_: u8,
    mut v_h_2520_: *mut LeanObject,
    mut v_semireducible_2521_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_semireducible_2521_);
    return v_semireducible_2521_;
}
pub unsafe fn l_Lean_ReducibilityStatus_semireducible_elim___boxed(
    mut v_motive_2522_: *mut LeanObject,
    mut v_t_2523_: *mut LeanObject,
    mut v_h_2524_: *mut LeanObject,
    mut v_semireducible_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2526_: u8 = 0;
    let mut v_res_2527_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2526_ = (lean_unbox(v_t_2523_) as u8);
    v_res_2527_ = l_Lean_ReducibilityStatus_semireducible_elim(
        v_motive_2522_,
        v_t_boxed_2526_,
        v_h_2524_,
        v_semireducible_2525_,
    );
    lean_dec(v_semireducible_2525_);
    return v_res_2527_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___redArg(
    mut v_irreducible_2528_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_irreducible_2528_);
    return v_irreducible_2528_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___redArg___boxed(
    mut v_irreducible_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2530_: *mut LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_ReducibilityStatus_irreducible_elim___redArg(v_irreducible_2529_);
    lean_dec(v_irreducible_2529_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim(
    mut v_motive_2531_: *mut LeanObject,
    mut v_t_2532_: u8,
    mut v_h_2533_: *mut LeanObject,
    mut v_irreducible_2534_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_irreducible_2534_);
    return v_irreducible_2534_;
}
pub unsafe fn l_Lean_ReducibilityStatus_irreducible_elim___boxed(
    mut v_motive_2535_: *mut LeanObject,
    mut v_t_2536_: *mut LeanObject,
    mut v_h_2537_: *mut LeanObject,
    mut v_irreducible_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2539_: u8 = 0;
    let mut v_res_2540_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2539_ = (lean_unbox(v_t_2536_) as u8);
    v_res_2540_ = l_Lean_ReducibilityStatus_irreducible_elim(
        v_motive_2535_,
        v_t_boxed_2539_,
        v_h_2537_,
        v_irreducible_2538_,
    );
    lean_dec(v_irreducible_2538_);
    return v_res_2540_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(
    mut v_implicitReducible_2541_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_implicitReducible_2541_);
    return v_implicitReducible_2541_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___redArg___boxed(
    mut v_implicitReducible_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2543_: *mut LeanObject = core::ptr::null_mut();
    v_res_2543_ =
        l_Lean_ReducibilityStatus_implicitReducible_elim___redArg(v_implicitReducible_2542_);
    lean_dec(v_implicitReducible_2542_);
    return v_res_2543_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim(
    mut v_motive_2544_: *mut LeanObject,
    mut v_t_2545_: u8,
    mut v_h_2546_: *mut LeanObject,
    mut v_implicitReducible_2547_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_implicitReducible_2547_);
    return v_implicitReducible_2547_;
}
pub unsafe fn l_Lean_ReducibilityStatus_implicitReducible_elim___boxed(
    mut v_motive_2548_: *mut LeanObject,
    mut v_t_2549_: *mut LeanObject,
    mut v_h_2550_: *mut LeanObject,
    mut v_implicitReducible_2551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_2552_: u8 = 0;
    let mut v_res_2553_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_2552_ = (lean_unbox(v_t_2549_) as u8);
    v_res_2553_ = l_Lean_ReducibilityStatus_implicitReducible_elim(
        v_motive_2548_,
        v_t_boxed_2552_,
        v_h_2550_,
        v_implicitReducible_2551_,
    );
    lean_dec(v_implicitReducible_2551_);
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
pub unsafe fn _init_l_Lean_instReprReducibilityStatus_repr___closed__8() -> *mut LeanObject {
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    v___x_2568_ = lean_unsigned_to_nat(2);
    v___x_2569_ = lean_nat_to_int(v___x_2568_);
    return v___x_2569_;
}
pub unsafe fn _init_l_Lean_instReprReducibilityStatus_repr___closed__9() -> *mut LeanObject {
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    v___x_2570_ = lean_unsigned_to_nat(1);
    v___x_2571_ = lean_nat_to_int(v___x_2570_);
    return v___x_2571_;
}
pub unsafe fn l_Lean_instReprReducibilityStatus_repr(
    mut v_x_2572_: u8,
    mut v_prec_2573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: u8 = 0;
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: u8 = 0;
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: u8 = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_2572_ {
                0 => {
                    v___x_2602_ = lean_unsigned_to_nat(1024);
                    v___x_2603_ = lean_nat_dec_le(v___x_2602_, v_prec_2573_);
                    if v___x_2603_ == 0 {
                        v___x_2604_ = lean_obj_once(
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
                        v___x_2605_ = lean_obj_once(
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
                    v___x_2606_ = lean_unsigned_to_nat(1024);
                    v___x_2607_ = lean_nat_dec_le(v___x_2606_, v_prec_2573_);
                    if v___x_2607_ == 0 {
                        v___x_2608_ = lean_obj_once(
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
                        v___x_2609_ = lean_obj_once(
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
                    v___x_2610_ = lean_unsigned_to_nat(1024);
                    v___x_2611_ = lean_nat_dec_le(v___x_2610_, v_prec_2573_);
                    if v___x_2611_ == 0 {
                        v___x_2612_ = lean_obj_once(
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
                        v___x_2613_ = lean_obj_once(
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
                    v___x_2614_ = lean_unsigned_to_nat(1024);
                    v___x_2615_ = lean_nat_dec_le(v___x_2614_, v_prec_2573_);
                    if v___x_2615_ == 0 {
                        v___x_2616_ = lean_obj_once(
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
                        v___x_2617_ = lean_obj_once(
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
                lean_inc(v___y_2575_);
                v___x_2577_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2577_, 0, v___y_2575_);
                lean_ctor_set(v___x_2577_, 1, v___x_2576_);
                v___x_2578_ = 0;
                v___x_2579_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2579_, 0, v___x_2577_);
                lean_ctor_set_uint8(
                    v___x_2579_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2578_,
                );
                v___x_2580_ = l_Repr_addAppParen(v___x_2579_, v_prec_2573_);
                return v___x_2580_;
            }
            2 => {
                v___x_2583_ = l_Lean_instReprReducibilityStatus_repr___closed__3;
                lean_inc(v___y_2582_);
                v___x_2584_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2584_, 0, v___y_2582_);
                lean_ctor_set(v___x_2584_, 1, v___x_2583_);
                v___x_2585_ = 0;
                v___x_2586_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2586_, 0, v___x_2584_);
                lean_ctor_set_uint8(
                    v___x_2586_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2585_,
                );
                v___x_2587_ = l_Repr_addAppParen(v___x_2586_, v_prec_2573_);
                return v___x_2587_;
            }
            3 => {
                v___x_2590_ = l_Lean_instReprReducibilityStatus_repr___closed__5;
                lean_inc(v___y_2589_);
                v___x_2591_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2591_, 0, v___y_2589_);
                lean_ctor_set(v___x_2591_, 1, v___x_2590_);
                v___x_2592_ = 0;
                v___x_2593_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2593_, 0, v___x_2591_);
                lean_ctor_set_uint8(
                    v___x_2593_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2592_,
                );
                v___x_2594_ = l_Repr_addAppParen(v___x_2593_, v_prec_2573_);
                return v___x_2594_;
            }
            4 => {
                v___x_2597_ = l_Lean_instReprReducibilityStatus_repr___closed__7;
                lean_inc(v___y_2596_);
                v___x_2598_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2598_, 0, v___y_2596_);
                lean_ctor_set(v___x_2598_, 1, v___x_2597_);
                v___x_2599_ = 0;
                v___x_2600_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                lean_ctor_set_uint8(
                    v___x_2600_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_2618_: *mut LeanObject,
    mut v_prec_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_233__boxed_2620_: u8 = 0;
    let mut v_res_2621_: *mut LeanObject = core::ptr::null_mut();
    v_x_233__boxed_2620_ = (lean_unbox(v_x_2618_) as u8);
    v_res_2621_ = l_Lean_instReprReducibilityStatus_repr(v_x_233__boxed_2620_, v_prec_2619_);
    lean_dec(v_prec_2619_);
    return v_res_2621_;
}
pub unsafe fn l_Lean_instBEqReducibilityStatus_beq(mut v_x_2624_: u8, mut v_y_2625_: u8) -> u8 {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: u8 = 0;
    v___x_2626_ = l_Lean_ReducibilityStatus_ctorIdx(v_x_2624_);
    v___x_2627_ = l_Lean_ReducibilityStatus_ctorIdx(v_y_2625_);
    v___x_2628_ = lean_nat_dec_eq(v___x_2626_, v___x_2627_);
    lean_dec(v___x_2627_);
    lean_dec(v___x_2626_);
    return v___x_2628_;
}
pub unsafe fn l_Lean_instBEqReducibilityStatus_beq___boxed(
    mut v_x_2629_: *mut LeanObject,
    mut v_y_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_2631_: u8 = 0;
    let mut v_y_18__boxed_2632_: u8 = 0;
    let mut v_res_2633_: u8 = 0;
    let mut v_r_2634_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_2631_ = (lean_unbox(v_x_2629_) as u8);
    v_y_18__boxed_2632_ = (lean_unbox(v_y_2630_) as u8);
    v_res_2633_ = l_Lean_instBEqReducibilityStatus_beq(v_x_17__boxed_2631_, v_y_18__boxed_2632_);
    v_r_2634_ = lean_box((v_res_2633_) as usize);
    return v_r_2634_;
}
pub unsafe fn l_Lean_ReducibilityStatus_toAttrString(mut v_x_2641_: u8) -> *mut LeanObject {
    match v_x_2641_ {
        0 => {
            let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
            v___x_2642_ = l_Lean_ReducibilityStatus_toAttrString___closed__0;
            return v___x_2642_;
        }
        1 => {
            let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
            v___x_2643_ = l_Lean_ReducibilityStatus_toAttrString___closed__1;
            return v___x_2643_;
        }
        2 => {
            let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
            v___x_2644_ = l_Lean_ReducibilityStatus_toAttrString___closed__2;
            return v___x_2644_;
        }
        _ => {
            let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
            v___x_2645_ = l_Lean_ReducibilityStatus_toAttrString___closed__3;
            return v___x_2645_;
        }
    }
}
pub unsafe fn l_Lean_ReducibilityStatus_toAttrString___boxed(
    mut v_x_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_40__boxed_2647_: u8 = 0;
    let mut v_res_2648_: *mut LeanObject = core::ptr::null_mut();
    v_x_40__boxed_2647_ = (lean_unbox(v_x_2646_) as u8);
    v_res_2648_ = l_Lean_ReducibilityStatus_toAttrString(v_x_40__boxed_2647_);
    return v_res_2648_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_s_2649_: *mut LeanObject,
    mut v_p_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2651_ = lean_ctor_get(v_p_2650_, 0);
    lean_inc(v_fst_2651_);
    v_snd_2652_ = lean_ctor_get(v_p_2650_, 1);
    lean_inc(v_snd_2652_);
    lean_dec_ref(v_p_2650_);
    v___x_2653_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_2651_,
        v_snd_2652_,
        v_s_2649_,
    );
    return v___x_2653_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_2654_: *mut LeanObject,
    mut v_x_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2655_) == 0 {
                    v_k_2656_ = lean_ctor_get(v_x_2655_, 1);
                    v_v_2657_ = lean_ctor_get(v_x_2655_, 2);
                    v_l_2658_ = lean_ctor_get(v_x_2655_, 3);
                    v_r_2659_ = lean_ctor_get(v_x_2655_, 4);
                    v___x_2660_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2654_, v_l_2658_);
                    lean_inc(v_v_2657_);
                    lean_inc(v_k_2656_);
                    v___x_2661_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2661_, 0, v_k_2656_);
                    lean_ctor_set(v___x_2661_, 1, v_v_2657_);
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
    mut v_init_2664_: *mut LeanObject,
    mut v_x_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2666_: *mut LeanObject = core::ptr::null_mut();
    v_res_2666_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2664_, v_x_2665_);
    lean_dec(v_x_2665_);
    return v_res_2666_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(
    mut v_a_2667_: *mut LeanObject,
    mut v_b_2668_: *mut LeanObject,
) -> u8 {
    let mut v_fst_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    v_fst_2669_ = lean_ctor_get(v_a_2667_, 0);
    v_fst_2670_ = lean_ctor_get(v_b_2668_, 0);
    v___x_2671_ = l_Lean_Name_quickLt(v_fst_2669_, v_fst_2670_);
    return v___x_2671_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0___boxed(
    mut v_a_2672_: *mut LeanObject,
    mut v_b_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2674_: u8 = 0;
    let mut v_r_2675_: *mut LeanObject = core::ptr::null_mut();
    v_res_2674_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_2672_, v_b_2673_);
    lean_dec_ref(v_b_2673_);
    lean_dec_ref(v_a_2672_);
    v_r_2675_ = lean_box((v_res_2674_) as usize);
    return v_r_2675_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_hi_2676_: *mut LeanObject,
    mut v_pivot_2677_: *mut LeanObject,
    mut v_as_2678_: *mut LeanObject,
    mut v_i_2679_: *mut LeanObject,
    mut v_k_2680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2681_: u8 = 0;
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: u8 = 0;
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2681_ = lean_nat_dec_lt(v_k_2680_, v_hi_2676_);
                if v___x_2681_ == 0 {
                    lean_dec(v_k_2680_);
                    v___x_2682_ = lean_array_fswap(v_as_2678_, v_i_2679_, v_hi_2676_);
                    v___x_2683_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2683_, 0, v_i_2679_);
                    lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                    return v___x_2683_;
                } else {
                    v___x_2684_ = lean_array_fget_borrowed(v_as_2678_, v_k_2680_);
                    v_fst_2685_ = lean_ctor_get(v___x_2684_, 0);
                    v_fst_2686_ = lean_ctor_get(v_pivot_2677_, 0);
                    v___x_2687_ = l_Lean_Name_quickLt(v_fst_2685_, v_fst_2686_);
                    if v___x_2687_ == 0 {
                        v___x_2688_ = lean_unsigned_to_nat(1);
                        v___x_2689_ = lean_nat_add(v_k_2680_, v___x_2688_);
                        lean_dec(v_k_2680_);
                        v_k_2680_ = v___x_2689_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2691_ = lean_array_fswap(v_as_2678_, v_i_2679_, v_k_2680_);
                        v___x_2692_ = lean_unsigned_to_nat(1);
                        v___x_2693_ = lean_nat_add(v_i_2679_, v___x_2692_);
                        lean_dec(v_i_2679_);
                        v___x_2694_ = lean_nat_add(v_k_2680_, v___x_2692_);
                        lean_dec(v_k_2680_);
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
    mut v_hi_2696_: *mut LeanObject,
    mut v_pivot_2697_: *mut LeanObject,
    mut v_as_2698_: *mut LeanObject,
    mut v_i_2699_: *mut LeanObject,
    mut v_k_2700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2701_: *mut LeanObject = core::ptr::null_mut();
    v_res_2701_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2696_, v_pivot_2697_, v_as_2698_, v_i_2699_, v_k_2700_);
    lean_dec_ref(v_pivot_2697_);
    lean_dec(v_hi_2696_);
    return v_res_2701_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(
    mut v_n_2702_: *mut LeanObject,
    mut v_as_2703_: *mut LeanObject,
    mut v_lo_2704_: *mut LeanObject,
    mut v_hi_2705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: u8 = 0;
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: u8 = 0;
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: u8 = 0;
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2717_ = lean_nat_dec_lt(v_lo_2704_, v_hi_2705_);
                if v___x_2717_ == 0 {
                    lean_dec(v_lo_2704_);
                    return v_as_2703_;
                } else {
                    v___x_2718_ = lean_nat_add(v_lo_2704_, v_hi_2705_);
                    v___x_2719_ = lean_unsigned_to_nat(1);
                    v_mid_2720_ = lean_nat_shiftr(v___x_2718_, v___x_2719_);
                    lean_dec(v___x_2718_);
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
                lean_inc_n(v_lo_2704_, 2);
                v___x_2709_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2705_, v_pivot_2708_, v___y_2707_, v_lo_2704_, v_lo_2704_);
                lean_dec(v_pivot_2708_);
                v_fst_2710_ = lean_ctor_get(v___x_2709_, 0);
                lean_inc(v_fst_2710_);
                v_snd_2711_ = lean_ctor_get(v___x_2709_, 1);
                lean_inc(v_snd_2711_);
                lean_dec_ref(v___x_2709_);
                v___x_2712_ = lean_nat_dec_le(v_hi_2705_, v_fst_2710_);
                if v___x_2712_ == 0 {
                    v___x_2713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2702_, v_snd_2711_, v_lo_2704_, v_fst_2710_);
                    v___x_2714_ = lean_unsigned_to_nat(1);
                    v___x_2715_ = lean_nat_add(v_fst_2710_, v___x_2714_);
                    lean_dec(v_fst_2710_);
                    v_as_2703_ = v___x_2713_;
                    v_lo_2704_ = v___x_2715_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2710_);
                    lean_dec(v_lo_2704_);
                    return v_snd_2711_;
                }
            }
            2 => {
                v___x_2723_ = lean_array_fget_borrowed(v___y_2722_, v_mid_2720_);
                v___x_2724_ = lean_array_fget_borrowed(v___y_2722_, v_hi_2705_);
                v___x_2725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v___x_2723_, v___x_2724_);
                if v___x_2725_ == 0 {
                    lean_dec(v_mid_2720_);
                    v___y_2707_ = v___y_2722_;
                    state = 1;
                    continue;
                } else {
                    v___x_2726_ = lean_array_fswap(v___y_2722_, v_mid_2720_, v_hi_2705_);
                    lean_dec(v_mid_2720_);
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
    mut v_n_2737_: *mut LeanObject,
    mut v_as_2738_: *mut LeanObject,
    mut v_lo_2739_: *mut LeanObject,
    mut v_hi_2740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2741_: *mut LeanObject = core::ptr::null_mut();
    v_res_2741_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2737_, v_as_2738_, v_lo_2739_, v_hi_2740_);
    lean_dec(v_hi_2740_);
    lean_dec(v_n_2737_);
    return v_res_2741_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_x_2744_: *mut LeanObject,
    mut v_s_2745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_unsigned_to_nat(0);
                v___x_2747_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                v_r_2748_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_2747_, v_s_2745_);
                v___x_2749_ = lean_array_get_size(v_r_2748_);
                v___x_2755_ = lean_nat_dec_eq(v___x_2749_, v___x_2746_);
                if v___x_2755_ == 0 {
                    v___x_2756_ = lean_unsigned_to_nat(1);
                    v___x_2757_ = lean_nat_sub(v___x_2749_, v___x_2756_);
                    v___x_2761_ = lean_nat_dec_le(v___x_2746_, v___x_2757_);
                    if v___x_2761_ == 0 {
                        lean_inc(v___x_2757_);
                        v___y_2759_ = v___x_2757_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2759_ = v___x_2746_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref_n(v_r_2748_, 2);
                    v___x_2762_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2762_, 0, v_r_2748_);
                    lean_ctor_set(v___x_2762_, 1, v_r_2748_);
                    lean_ctor_set(v___x_2762_, 2, v_r_2748_);
                    return v___x_2762_;
                }
            }
            1 => {
                v___x_2753_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2749_, v_r_2748_, v___y_2751_, v___y_2752_);
                lean_dec(v___y_2752_);
                lean_inc_ref_n(v___x_2753_, 2);
                v___x_2754_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                lean_ctor_set(v___x_2754_, 1, v___x_2753_);
                lean_ctor_set(v___x_2754_, 2, v___x_2753_);
                return v___x_2754_;
            }
            2 => {
                v___x_2760_ = lean_nat_dec_le(v___y_2759_, v___x_2757_);
                if v___x_2760_ == 0 {
                    lean_dec(v___x_2757_);
                    lean_inc(v___y_2759_);
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
    mut v_x_2763_: *mut LeanObject,
    mut v_s_2764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2765_: *mut LeanObject = core::ptr::null_mut();
    v_res_2765_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_x_2763_, v_s_2764_);
    lean_dec(v_s_2764_);
    lean_dec_ref(v_x_2763_);
    return v_res_2765_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_s_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2779_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__2___closed__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                if lean_obj_tag(v_s_2778_) == 0 {
                    v_size_2785_ = lean_ctor_get(v_s_2778_, 0);
                    lean_inc(v_size_2785_);
                    lean_dec_ref_known(v_s_2778_, 5);
                    v___y_2781_ = v_size_2785_;
                    state = 1;
                    continue;
                } else {
                    v___x_2786_ = lean_unsigned_to_nat(0);
                    v___y_2781_ = v___x_2786_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2782_ = l_Nat_reprFast(v___y_2781_);
                v___x_2783_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2783_, 0, v___x_2782_);
                v___x_2784_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2784_, 0, v___x_2779_);
                lean_ctor_set(v___x_2784_, 1, v___x_2783_);
                return v___x_2784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(
    mut v_newState_2787_: *mut LeanObject,
    mut v_x_2788_: *mut LeanObject,
    mut v_x_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2789_) == 0 {
                    return v_x_2788_;
                } else {
                    v_head_2790_ = lean_ctor_get(v_x_2789_, 0);
                    lean_inc(v_head_2790_);
                    v_tail_2791_ = lean_ctor_get(v_x_2789_, 1);
                    lean_inc(v_tail_2791_);
                    lean_dec_ref_known(v_x_2789_, 2);
                    v___x_2792_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_newState_2787_, v_head_2790_);
                    if lean_obj_tag(v___x_2792_) == 1 {
                        v_val_2793_ = lean_ctor_get(v___x_2792_, 0);
                        lean_inc(v_val_2793_);
                        lean_dec_ref_known(v___x_2792_, 1);
                        v___x_2794_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_head_2790_, v_val_2793_, v_x_2788_);
                        v_x_2788_ = v___x_2794_;
                        v_x_2789_ = v_tail_2791_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2792_);
                        lean_dec(v_head_2790_);
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
    mut v_newState_2797_: *mut LeanObject,
    mut v_x_2798_: *mut LeanObject,
    mut v_x_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_2797_, v_x_2798_, v_x_2799_);
    lean_dec(v_newState_2797_);
    return v_res_2800_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___oldState_2801_: *mut LeanObject,
    mut v_newState_2802_: *mut LeanObject,
    mut v_newItems_2803_: *mut LeanObject,
    mut v_otherState_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    v___x_2805_ = l_List_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__2(v_newState_2802_, v_otherState_2804_, v_newItems_2803_);
    return v___x_2805_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___oldState_2806_: *mut LeanObject,
    mut v_newState_2807_: *mut LeanObject,
    mut v_newItems_2808_: *mut LeanObject,
    mut v_otherState_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2810_: *mut LeanObject = core::ptr::null_mut();
    v_res_2810_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__3_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___oldState_2806_, v_newState_2807_, v_newItems_2808_, v_otherState_2809_);
    lean_dec(v_newState_2807_);
    lean_dec(v___oldState_2806_);
    return v_res_2810_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v_m_2811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: u8 = 0;
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: u8 = 0;
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2812_ = lean_unsigned_to_nat(0);
                v___x_2813_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__1___closed__0_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
                v_r_2814_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v___x_2813_, v_m_2811_);
                v___x_2815_ = lean_array_get_size(v_r_2814_);
                v___x_2816_ = lean_nat_dec_eq(v___x_2815_, v___x_2812_);
                if v___x_2816_ == 0 {
                    v___x_2817_ = lean_unsigned_to_nat(1);
                    v___x_2818_ = lean_nat_sub(v___x_2815_, v___x_2817_);
                    v___x_2824_ = lean_nat_dec_le(v___x_2812_, v___x_2818_);
                    if v___x_2824_ == 0 {
                        lean_inc(v___x_2818_);
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
                    lean_dec(v___x_2818_);
                    lean_inc(v___y_2820_);
                    v___x_2822_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2815_, v_r_2814_, v___y_2820_, v___y_2820_);
                    lean_dec(v___y_2820_);
                    return v___x_2822_;
                } else {
                    v___x_2823_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v___x_2815_, v_r_2814_, v___y_2820_, v___x_2818_);
                    lean_dec(v___x_2818_);
                    return v___x_2823_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v_m_2825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2826_: *mut LeanObject = core::ptr::null_mut();
    v_res_2826_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__4_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v_m_2825_);
    lean_dec(v_m_2825_);
    return v_res_2826_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___x_2827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    v___x_2829_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2829_, 0, v___x_2827_);
    return v___x_2829_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___x_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2832_: *mut LeanObject = core::ptr::null_mut();
    v_res_2832_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__5_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_2830_);
    return v_res_2832_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(
    mut v___x_2833_: *mut LeanObject,
    mut v_x_2834_: *mut LeanObject,
    mut v_x_2835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    v___x_2837_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2837_, 0, v___x_2833_);
    return v___x_2837_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v___x_2838_: *mut LeanObject,
    mut v_x_2839_: *mut LeanObject,
    mut v_x_2840_: *mut LeanObject,
    mut v___y_2841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2842_: *mut LeanObject = core::ptr::null_mut();
    v_res_2842_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__6_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_(v___x_2838_, v_x_2839_, v_x_2840_);
    lean_dec_ref(v_x_2840_);
    lean_dec_ref(v_x_2839_);
    return v_res_2842_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    v___x_2872_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_;
    v___x_2873_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2872_);
    return v___x_2873_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2____boxed(
    mut v_a_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2875_: *mut LeanObject = core::ptr::null_mut();
    v_res_2875_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
    return v_res_2875_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(
    mut v_init_2876_: *mut LeanObject,
    mut v_t_2877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    v___x_2878_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0_spec__0(v_init_2876_, v_t_2877_);
    return v___x_2878_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_2879_: *mut LeanObject,
    mut v_t_2880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2881_: *mut LeanObject = core::ptr::null_mut();
    v_res_2881_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__0(v_init_2879_, v_t_2880_);
    lean_dec(v_t_2880_);
    return v_res_2881_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(
    mut v_n_2882_: *mut LeanObject,
    mut v_as_2883_: *mut LeanObject,
    mut v_lo_2884_: *mut LeanObject,
    mut v_hi_2885_: *mut LeanObject,
    mut v_w_2886_: *mut LeanObject,
    mut v_hlo_2887_: *mut LeanObject,
    mut v_hhi_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v___x_2889_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg(v_n_2882_, v_as_2883_, v_lo_2884_, v_hi_2885_);
    return v___x_2889_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___boxed(
    mut v_n_2890_: *mut LeanObject,
    mut v_as_2891_: *mut LeanObject,
    mut v_lo_2892_: *mut LeanObject,
    mut v_hi_2893_: *mut LeanObject,
    mut v_w_2894_: *mut LeanObject,
    mut v_hlo_2895_: *mut LeanObject,
    mut v_hhi_2896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2897_: *mut LeanObject = core::ptr::null_mut();
    v_res_2897_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1(v_n_2890_, v_as_2891_, v_lo_2892_, v_hi_2893_, v_w_2894_, v_hlo_2895_, v_hhi_2896_);
    lean_dec(v_hi_2893_);
    lean_dec(v_n_2890_);
    return v_res_2897_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(
    mut v_n_2898_: *mut LeanObject,
    mut v_lo_2899_: *mut LeanObject,
    mut v_hi_2900_: *mut LeanObject,
    mut v_hhi_2901_: *mut LeanObject,
    mut v_pivot_2902_: *mut LeanObject,
    mut v_as_2903_: *mut LeanObject,
    mut v_i_2904_: *mut LeanObject,
    mut v_k_2905_: *mut LeanObject,
    mut v_ilo_2906_: *mut LeanObject,
    mut v_ik_2907_: *mut LeanObject,
    mut v_w_2908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2909_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_2900_, v_pivot_2902_, v_as_2903_, v_i_2904_, v_k_2905_);
    return v___x_2909_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_n_2910_: *mut LeanObject,
    mut v_lo_2911_: *mut LeanObject,
    mut v_hi_2912_: *mut LeanObject,
    mut v_hhi_2913_: *mut LeanObject,
    mut v_pivot_2914_: *mut LeanObject,
    mut v_as_2915_: *mut LeanObject,
    mut v_i_2916_: *mut LeanObject,
    mut v_k_2917_: *mut LeanObject,
    mut v_ilo_2918_: *mut LeanObject,
    mut v_ik_2919_: *mut LeanObject,
    mut v_w_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1_spec__2(v_n_2910_, v_lo_2911_, v_hi_2912_, v_hhi_2913_, v_pivot_2914_, v_as_2915_, v_i_2916_, v_k_2917_, v_ilo_2918_, v_ik_2919_, v_w_2920_);
    lean_dec_ref(v_pivot_2914_);
    lean_dec(v_hi_2912_);
    lean_dec(v_lo_2911_);
    lean_dec(v_n_2910_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(
    mut v_m_2922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_2923_: u8 = 0;
    let mut v_map_u2081_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_2923_ = lean_ctor_get_uint8(
                    v_m_2922_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_2923_ == 0 {
                    return v_m_2922_;
                } else {
                    v_map_u2081_2924_ = lean_ctor_get(v_m_2922_, 0);
                    v_map_u2082_2925_ = lean_ctor_get(v_m_2922_, 1);
                    v_isSharedCheck_2933_ = (!lean_is_exclusive(v_m_2922_)) as u8;
                    if v_isSharedCheck_2933_ == 0 {
                        v___x_2927_ = v_m_2922_;
                        v_isShared_2928_ = v_isSharedCheck_2933_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_2925_);
                        lean_inc(v_map_u2081_2924_);
                        lean_dec(v_m_2922_);
                        v___x_2927_ = lean_box(0);
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
                    v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_map_u2081_2924_);
                    lean_ctor_set(v_reuseFailAlloc_2932_, 1, v_map_u2082_2925_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_2931_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2929_,
                );
                return v___x_2931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0(
    mut v_00_u03b2_2934_: *mut LeanObject,
    mut v_m_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Lean_SMap_switch___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__0___redArg(v_m_2935_);
    return v___x_2936_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(
    mut v_x_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    v___x_2939_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2939_, 0, v_a_2938_);
    lean_inc_ref_n(v___x_2939_, 2);
    v___x_2940_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2940_, 0, v___x_2939_);
    lean_ctor_set(v___x_2940_, 1, v___x_2939_);
    lean_ctor_set(v___x_2940_, 2, v___x_2939_);
    return v___x_2940_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(
    mut v_x_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_(v_x_2941_, v_a_2942_);
    lean_dec_ref(v_x_2941_);
    return v_res_2943_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0()
-> u64 {
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: u64 = 0;
    v___x_2944_ = lean_unsigned_to_nat(1723);
    v___x_2945_ = lean_uint64_of_nat(v___x_2944_);
    return v___x_2945_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(
    mut v_x_2946_: *mut LeanObject,
    mut v_x_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2953_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: u64 = 0;
    let mut v_hash_2975_: u64 = 0;
    let mut v_isSharedCheck_2976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2947_) == 0 {
                    return v_x_2946_;
                } else {
                    v_key_2948_ = lean_ctor_get(v_x_2947_, 0);
                    v_value_2949_ = lean_ctor_get(v_x_2947_, 1);
                    v_tail_2950_ = lean_ctor_get(v_x_2947_, 2);
                    v_isSharedCheck_2976_ = (!lean_is_exclusive(v_x_2947_)) as u8;
                    if v_isSharedCheck_2976_ == 0 {
                        v___x_2952_ = v_x_2947_;
                        v_isShared_2953_ = v_isSharedCheck_2976_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2950_);
                        lean_inc(v_value_2949_);
                        lean_inc(v_key_2948_);
                        lean_dec(v_x_2947_);
                        v___x_2952_ = lean_box(0);
                        v_isShared_2953_ = v_isSharedCheck_2976_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2954_ = lean_array_get_size(v_x_2946_);
                if lean_obj_tag(v_key_2948_) == 0 {
                    v___x_2974_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_2956_ = v___x_2974_;
                    state = 2;
                    continue;
                } else {
                    v_hash_2975_ = lean_ctor_get_uint64(
                        v_key_2948_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_2968_);
                if v_isShared_2953_ == 0 {
                    lean_ctor_set(v___x_2952_, 2, v___x_2968_);
                    v___x_2970_ = v___x_2952_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_key_2948_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_value_2949_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 2, v___x_2968_);
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
    mut v_i_2977_: *mut LeanObject,
    mut v_source_2978_: *mut LeanObject,
    mut v_target_2979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v_es_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2980_ = lean_array_get_size(v_source_2978_);
                v___x_2981_ = lean_nat_dec_lt(v_i_2977_, v___x_2980_);
                if v___x_2981_ == 0 {
                    lean_dec_ref(v_source_2978_);
                    lean_dec(v_i_2977_);
                    return v_target_2979_;
                } else {
                    v_es_2982_ = lean_array_fget(v_source_2978_, v_i_2977_);
                    v___x_2983_ = lean_box(0);
                    v_source_2984_ = lean_array_fset(v_source_2978_, v_i_2977_, v___x_2983_);
                    v_target_2985_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_target_2979_, v_es_2982_);
                    v___x_2986_ = lean_unsigned_to_nat(1);
                    v___x_2987_ = lean_nat_add(v_i_2977_, v___x_2986_);
                    lean_dec(v_i_2977_);
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
    mut v_data_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    v___x_2990_ = lean_array_get_size(v_data_2989_);
    v___x_2991_ = lean_unsigned_to_nat(2);
    v_nbuckets_2992_ = lean_nat_mul(v___x_2990_, v___x_2991_);
    v___x_2993_ = lean_unsigned_to_nat(0);
    v___x_2994_ = lean_box(0);
    v___x_2995_ = lean_mk_array(v_nbuckets_2992_, v___x_2994_);
    v___x_2996_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v___x_2993_, v_data_2989_, v___x_2995_);
    return v___x_2996_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(
    mut v_a_2997_: *mut LeanObject,
    mut v_x_2998_: *mut LeanObject,
) -> u8 {
    let mut v___x_2999_: u8 = 0;
    let mut v_key_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2998_) == 0 {
                    v___x_2999_ = 0;
                    return v___x_2999_;
                } else {
                    v_key_3000_ = lean_ctor_get(v_x_2998_, 0);
                    v_tail_3001_ = lean_ctor_get(v_x_2998_, 2);
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
    mut v_a_3004_: *mut LeanObject,
    mut v_x_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3006_: u8 = 0;
    let mut v_r_3007_: *mut LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_3004_, v_x_3005_);
    lean_dec(v_x_3005_);
    lean_dec(v_a_3004_);
    v_r_3007_ = lean_box((v_res_3006_) as usize);
    return v_r_3007_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(
    mut v_a_3008_: *mut LeanObject,
    mut v_b_3009_: *mut LeanObject,
    mut v_x_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3017_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3010_) == 0 {
                    lean_dec(v_b_3009_);
                    lean_dec(v_a_3008_);
                    return v_x_3010_;
                } else {
                    v_key_3011_ = lean_ctor_get(v_x_3010_, 0);
                    v_value_3012_ = lean_ctor_get(v_x_3010_, 1);
                    v_tail_3013_ = lean_ctor_get(v_x_3010_, 2);
                    v_isSharedCheck_3025_ = (!lean_is_exclusive(v_x_3010_)) as u8;
                    if v_isSharedCheck_3025_ == 0 {
                        v___x_3015_ = v_x_3010_;
                        v_isShared_3016_ = v_isSharedCheck_3025_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3013_);
                        lean_inc(v_value_3012_);
                        lean_inc(v_key_3011_);
                        lean_dec(v_x_3010_);
                        v___x_3015_ = lean_box(0);
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
                        lean_ctor_set(v___x_3015_, 2, v___x_3018_);
                        v___x_3020_ = v___x_3015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_key_3011_);
                        lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_value_3012_);
                        lean_ctor_set(v_reuseFailAlloc_3021_, 2, v___x_3018_);
                        v___x_3020_ = v_reuseFailAlloc_3021_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3012_);
                    lean_dec(v_key_3011_);
                    if v_isShared_3016_ == 0 {
                        lean_ctor_set(v___x_3015_, 1, v_b_3009_);
                        lean_ctor_set(v___x_3015_, 0, v_a_3008_);
                        v___x_3023_ = v___x_3015_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3024_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_a_3008_);
                        lean_ctor_set(v_reuseFailAlloc_3024_, 1, v_b_3009_);
                        lean_ctor_set(v_reuseFailAlloc_3024_, 2, v_tail_3013_);
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
    mut v_m_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_b_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: u8 = 0;
    let mut v_val_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u64 = 0;
    let mut v_hash_3075_: u64 = 0;
    let mut v_isSharedCheck_3076_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3029_ = lean_ctor_get(v_m_3026_, 0);
                v_buckets_3030_ = lean_ctor_get(v_m_3026_, 1);
                v_isSharedCheck_3076_ = (!lean_is_exclusive(v_m_3026_)) as u8;
                if v_isSharedCheck_3076_ == 0 {
                    v___x_3032_ = v_m_3026_;
                    v_isShared_3033_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3030_);
                    lean_inc(v_size_3029_);
                    lean_dec(v_m_3026_);
                    v___x_3032_ = lean_box(0);
                    v_isShared_3033_ = v_isSharedCheck_3076_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3034_ = lean_array_get_size(v_buckets_3030_);
                if lean_obj_tag(v_a_3027_) == 0 {
                    v___x_3074_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3036_ = v___x_3074_;
                    state = 2;
                    continue;
                } else {
                    v_hash_3075_ = lean_ctor_get_uint64(
                        v_a_3027_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    v___x_3050_ = lean_unsigned_to_nat(1);
                    v_size_x27_3051_ = lean_nat_add(v_size_3029_, v___x_3050_);
                    lean_dec(v_size_3029_);
                    lean_inc(v_bkt_3048_);
                    v___x_3052_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3052_, 0, v_a_3027_);
                    lean_ctor_set(v___x_3052_, 1, v_b_3028_);
                    lean_ctor_set(v___x_3052_, 2, v_bkt_3048_);
                    v_buckets_x27_3053_ =
                        lean_array_uset(v_buckets_3030_, v___x_3047_, v___x_3052_);
                    v___x_3054_ = lean_unsigned_to_nat(4);
                    v___x_3055_ = lean_nat_mul(v_size_x27_3051_, v___x_3054_);
                    v___x_3056_ = lean_unsigned_to_nat(3);
                    v___x_3057_ = lean_nat_div(v___x_3055_, v___x_3056_);
                    lean_dec(v___x_3055_);
                    v___x_3058_ = lean_array_get_size(v_buckets_x27_3053_);
                    v___x_3059_ = lean_nat_dec_le(v___x_3057_, v___x_3058_);
                    lean_dec(v___x_3057_);
                    if v___x_3059_ == 0 {
                        v_val_3060_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_buckets_x27_3053_);
                        if v_isShared_3033_ == 0 {
                            lean_ctor_set(v___x_3032_, 1, v_val_3060_);
                            lean_ctor_set(v___x_3032_, 0, v_size_x27_3051_);
                            v___x_3062_ = v___x_3032_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3063_, 0, v_size_x27_3051_);
                            lean_ctor_set(v_reuseFailAlloc_3063_, 1, v_val_3060_);
                            v___x_3062_ = v_reuseFailAlloc_3063_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_3033_ == 0 {
                            lean_ctor_set(v___x_3032_, 1, v_buckets_x27_3053_);
                            lean_ctor_set(v___x_3032_, 0, v_size_x27_3051_);
                            v___x_3065_ = v___x_3032_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3066_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3066_, 0, v_size_x27_3051_);
                            lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_buckets_x27_3053_);
                            v___x_3065_ = v_reuseFailAlloc_3066_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3048_);
                    v___x_3067_ = lean_box(0);
                    v_buckets_x27_3068_ =
                        lean_array_uset(v_buckets_3030_, v___x_3047_, v___x_3067_);
                    v___x_3069_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_3027_, v_b_3028_, v_bkt_3048_);
                    v___x_3070_ = lean_array_uset(v_buckets_x27_3068_, v___x_3047_, v___x_3069_);
                    if v_isShared_3033_ == 0 {
                        lean_ctor_set(v___x_3032_, 1, v___x_3070_);
                        v___x_3072_ = v___x_3032_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3073_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_size_3029_);
                        lean_ctor_set(v_reuseFailAlloc_3073_, 1, v___x_3070_);
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
    mut v_x_3077_: *mut LeanObject,
    mut v_x_3078_: *mut LeanObject,
    mut v_x_3079_: *mut LeanObject,
    mut v_x_3080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: u8 = 0;
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_3081_ = lean_ctor_get(v_x_3077_, 0);
                v_vs_3082_ = lean_ctor_get(v_x_3077_, 1);
                v_isSharedCheck_3106_ = (!lean_is_exclusive(v_x_3077_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3084_ = v_x_3077_;
                    v_isShared_3085_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_3082_);
                    lean_inc(v_ks_3081_);
                    lean_dec(v_x_3077_);
                    v___x_3084_ = lean_box(0);
                    v_isShared_3085_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3086_ = lean_array_get_size(v_ks_3081_);
                v___x_3087_ = lean_nat_dec_lt(v_x_3078_, v___x_3086_);
                if v___x_3087_ == 0 {
                    lean_dec(v_x_3078_);
                    v___x_3088_ = lean_array_push(v_ks_3081_, v_x_3079_);
                    v___x_3089_ = lean_array_push(v_vs_3082_, v_x_3080_);
                    if v_isShared_3085_ == 0 {
                        lean_ctor_set(v___x_3084_, 1, v___x_3089_);
                        lean_ctor_set(v___x_3084_, 0, v___x_3088_);
                        v___x_3091_ = v___x_3084_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3088_);
                        lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3089_);
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
                            v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_ks_3081_);
                            lean_ctor_set(v_reuseFailAlloc_3100_, 1, v_vs_3082_);
                            v___x_3096_ = v_reuseFailAlloc_3100_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_3101_ = lean_array_fset(v_ks_3081_, v_x_3078_, v_x_3079_);
                        v___x_3102_ = lean_array_fset(v_vs_3082_, v_x_3078_, v_x_3080_);
                        lean_dec(v_x_3078_);
                        if v_isShared_3085_ == 0 {
                            lean_ctor_set(v___x_3084_, 1, v___x_3102_);
                            lean_ctor_set(v___x_3084_, 0, v___x_3101_);
                            v___x_3104_ = v___x_3084_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3101_);
                            lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3102_);
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
                v___x_3097_ = lean_unsigned_to_nat(1);
                v___x_3098_ = lean_nat_add(v_x_3078_, v___x_3097_);
                lean_dec(v_x_3078_);
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
    mut v_n_3107_: *mut LeanObject,
    mut v_k_3108_: *mut LeanObject,
    mut v_v_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    v___x_3110_ = lean_unsigned_to_nat(0);
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
    v___x_3116_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__0);
    v___x_3117_ = lean_usize_sub(v___x_3116_, v___x_3115_);
    return v___x_3117_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    v___x_3118_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_3118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(
    mut v_x_3119_: *mut LeanObject,
    mut v_x_3120_: usize,
    mut v_x_3121_: usize,
    mut v_x_3122_: *mut LeanObject,
    mut v_x_3123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: usize = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: usize = 0;
    let mut v___x_3128_: usize = 0;
    let mut v_j_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v_v_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: u8 = 0;
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v_node_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3159_: u8 = 0;
    let mut v___x_3160_: usize = 0;
    let mut v___x_3161_: usize = 0;
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3166_: u8 = 0;
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_unused_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: u8 = 0;
    let mut v_ks_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: usize = 0;
    let mut v___x_3186_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3119_) == 0 {
                    v_es_3124_ = lean_ctor_get(v_x_3119_, 0);
                    v___x_3125_ = 5usize;
                    v___x_3126_ = 1usize;
                    v___x_3127_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_3128_ = lean_usize_land(v_x_3120_, v___x_3127_);
                    v_j_3129_ = lean_usize_to_nat(v___x_3128_);
                    v___x_3130_ = lean_array_get_size(v_es_3124_);
                    v___x_3131_ = lean_nat_dec_lt(v_j_3129_, v___x_3130_);
                    if v___x_3131_ == 0 {
                        lean_dec(v_j_3129_);
                        lean_dec(v_x_3123_);
                        lean_dec(v_x_3122_);
                        return v_x_3119_;
                    } else {
                        lean_inc_ref(v_es_3124_);
                        v_isSharedCheck_3168_ = (!lean_is_exclusive(v_x_3119_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v_unused_3169_ = lean_ctor_get(v_x_3119_, 0);
                            lean_dec(v_unused_3169_);
                            v___x_3133_ = v_x_3119_;
                            v_isShared_3134_ = v_isSharedCheck_3168_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_3119_);
                            v___x_3133_ = lean_box(0);
                            v_isShared_3134_ = v_isSharedCheck_3168_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_3170_ = lean_ctor_get(v_x_3119_, 0);
                    v_vs_3171_ = lean_ctor_get(v_x_3119_, 1);
                    v_isSharedCheck_3191_ = (!lean_is_exclusive(v_x_3119_)) as u8;
                    if v_isSharedCheck_3191_ == 0 {
                        v___x_3173_ = v_x_3119_;
                        v_isShared_3174_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_3171_);
                        lean_inc(v_ks_3170_);
                        lean_dec(v_x_3119_);
                        v___x_3173_ = lean_box(0);
                        v_isShared_3174_ = v_isSharedCheck_3191_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3135_ = lean_array_fget(v_es_3124_, v_j_3129_);
                v___x_3136_ = lean_box(0);
                v_xs_x27_3137_ = lean_array_fset(v_es_3124_, v_j_3129_, v___x_3136_);
                match lean_obj_tag(v_v_3135_) {
                    0 => {
                        v_key_3144_ = lean_ctor_get(v_v_3135_, 0);
                        v_val_3145_ = lean_ctor_get(v_v_3135_, 1);
                        v_isSharedCheck_3155_ = (!lean_is_exclusive(v_v_3135_)) as u8;
                        if v_isSharedCheck_3155_ == 0 {
                            v___x_3147_ = v_v_3135_;
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_3145_);
                            lean_inc(v_key_3144_);
                            lean_dec(v_v_3135_);
                            v___x_3147_ = lean_box(0);
                            v_isShared_3148_ = v_isSharedCheck_3155_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_3156_ = lean_ctor_get(v_v_3135_, 0);
                        v_isSharedCheck_3166_ = (!lean_is_exclusive(v_v_3135_)) as u8;
                        if v_isSharedCheck_3166_ == 0 {
                            v___x_3158_ = v_v_3135_;
                            v_isShared_3159_ = v_isSharedCheck_3166_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_3156_);
                            lean_dec(v_v_3135_);
                            v___x_3158_ = lean_box(0);
                            v_isShared_3159_ = v_isSharedCheck_3166_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_3167_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_3167_, 0, v_x_3122_);
                        lean_ctor_set(v___x_3167_, 1, v_x_3123_);
                        v___y_3139_ = v___x_3167_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3140_ = lean_array_fset(v_xs_x27_3137_, v_j_3129_, v___y_3139_);
                lean_dec(v_j_3129_);
                if v_isShared_3134_ == 0 {
                    lean_ctor_set(v___x_3133_, 0, v___x_3140_);
                    v___x_3142_ = v___x_3133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3140_);
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
                    lean_del_object(v___x_3147_);
                    v___x_3150_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_3144_,
                        v_val_3145_,
                        v_x_3122_,
                        v_x_3123_,
                    );
                    v___x_3151_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3151_, 0, v___x_3150_);
                    v___y_3139_ = v___x_3151_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_3145_);
                    lean_dec(v_key_3144_);
                    if v_isShared_3148_ == 0 {
                        lean_ctor_set(v___x_3147_, 1, v_x_3123_);
                        lean_ctor_set(v___x_3147_, 0, v_x_3122_);
                        v___x_3153_ = v___x_3147_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_x_3122_);
                        lean_ctor_set(v_reuseFailAlloc_3154_, 1, v_x_3123_);
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
                    lean_ctor_set(v___x_3158_, 0, v___x_3162_);
                    v___x_3164_ = v___x_3158_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3162_);
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
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_ks_3170_);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_vs_3171_);
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
                    v___x_3188_ = lean_unsigned_to_nat(4);
                    v___x_3189_ = lean_nat_dec_lt(v___x_3187_, v___x_3188_);
                    lean_dec(v___x_3187_);
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
                    v_ks_3180_ = lean_ctor_get(v_newNode_3177_, 0);
                    lean_inc_ref(v_ks_3180_);
                    v_vs_3181_ = lean_ctor_get(v_newNode_3177_, 1);
                    lean_inc_ref(v_vs_3181_);
                    lean_dec_ref(v_newNode_3177_);
                    v___x_3182_ = lean_unsigned_to_nat(0);
                    v___x_3183_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__2);
                    v___x_3184_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_x_3121_, v_ks_3180_, v_vs_3181_, v___x_3182_, v___x_3183_);
                    lean_dec_ref(v_vs_3181_);
                    lean_dec_ref(v_ks_3180_);
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
    mut v_keys_3193_: *mut LeanObject,
    mut v_vals_3194_: *mut LeanObject,
    mut v_i_3195_: *mut LeanObject,
    mut v_entries_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v_k_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: u64 = 0;
    let mut v_h_3203_: usize = 0;
    let mut v___x_3204_: usize = 0;
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: usize = 0;
    let mut v___x_3207_: usize = 0;
    let mut v___x_3208_: usize = 0;
    let mut v_h_3209_: usize = 0;
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: u64 = 0;
    let mut v_hash_3214_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3197_ = lean_array_get_size(v_keys_3193_);
                v___x_3198_ = lean_nat_dec_lt(v_i_3195_, v___x_3197_);
                if v___x_3198_ == 0 {
                    lean_dec(v_i_3195_);
                    return v_entries_3196_;
                } else {
                    v_k_3199_ = lean_array_fget_borrowed(v_keys_3193_, v_i_3195_);
                    v_v_3200_ = lean_array_fget_borrowed(v_vals_3194_, v_i_3195_);
                    if lean_obj_tag(v_k_3199_) == 0 {
                        v___x_3213_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                        v___y_3202_ = v___x_3213_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_3214_ = lean_ctor_get_uint64(
                            v_k_3199_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                v___x_3205_ = lean_unsigned_to_nat(1);
                v___x_3206_ = 1usize;
                v___x_3207_ = lean_usize_sub(v_depth_3192_, v___x_3206_);
                v___x_3208_ = lean_usize_mul(v___x_3204_, v___x_3207_);
                v_h_3209_ = lean_usize_shift_right(v_h_3203_, v___x_3208_);
                v___x_3210_ = lean_nat_add(v_i_3195_, v___x_3205_);
                lean_dec(v_i_3195_);
                lean_inc(v_v_3200_);
                lean_inc(v_k_3199_);
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
    mut v_depth_3215_: *mut LeanObject,
    mut v_keys_3216_: *mut LeanObject,
    mut v_vals_3217_: *mut LeanObject,
    mut v_i_3218_: *mut LeanObject,
    mut v_entries_3219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3220_: usize = 0;
    let mut v_res_3221_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3220_ = lean_unbox_usize(v_depth_3215_);
    lean_dec(v_depth_3215_);
    v_res_3221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_3220_, v_keys_3216_, v_vals_3217_, v_i_3218_, v_entries_3219_);
    lean_dec_ref(v_vals_3217_);
    lean_dec_ref(v_keys_3216_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___boxed(
    mut v_x_3222_: *mut LeanObject,
    mut v_x_3223_: *mut LeanObject,
    mut v_x_3224_: *mut LeanObject,
    mut v_x_3225_: *mut LeanObject,
    mut v_x_3226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1110__boxed_3227_: usize = 0;
    let mut v_x_1111__boxed_3228_: usize = 0;
    let mut v_res_3229_: *mut LeanObject = core::ptr::null_mut();
    v_x_1110__boxed_3227_ = lean_unbox_usize(v_x_3223_);
    lean_dec(v_x_3223_);
    v_x_1111__boxed_3228_ = lean_unbox_usize(v_x_3224_);
    lean_dec(v_x_3224_);
    v_res_3229_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3222_, v_x_1110__boxed_3227_, v_x_1111__boxed_3228_, v_x_3225_, v_x_3226_);
    return v_res_3229_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(
    mut v_x_3230_: *mut LeanObject,
    mut v_x_3231_: *mut LeanObject,
    mut v_x_3232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3234_: u64 = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: u64 = 0;
    let mut v_hash_3239_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3231_) == 0 {
                    v___x_3238_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3234_ = v___x_3238_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3239_ = lean_ctor_get_uint64(
                        v_x_3231_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_x_3240_: *mut LeanObject,
    mut v_x_3241_: *mut LeanObject,
    mut v_x_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_3243_: u8 = 0;
    let mut v_map_u2081_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3248_: u8 = 0;
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3253_: u8 = 0;
    let mut v_map_u2081_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_u2082_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_stage_u2081_3243_ = lean_ctor_get_uint8(
                    v_x_3240_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                );
                if v_stage_u2081_3243_ == 0 {
                    v_map_u2081_3244_ = lean_ctor_get(v_x_3240_, 0);
                    v_map_u2082_3245_ = lean_ctor_get(v_x_3240_, 1);
                    v_isSharedCheck_3253_ = (!lean_is_exclusive(v_x_3240_)) as u8;
                    if v_isSharedCheck_3253_ == 0 {
                        v___x_3247_ = v_x_3240_;
                        v_isShared_3248_ = v_isSharedCheck_3253_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_3245_);
                        lean_inc(v_map_u2081_3244_);
                        lean_dec(v_x_3240_);
                        v___x_3247_ = lean_box(0);
                        v_isShared_3248_ = v_isSharedCheck_3253_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_map_u2081_3254_ = lean_ctor_get(v_x_3240_, 0);
                    v_map_u2082_3255_ = lean_ctor_get(v_x_3240_, 1);
                    v_isSharedCheck_3263_ = (!lean_is_exclusive(v_x_3240_)) as u8;
                    if v_isSharedCheck_3263_ == 0 {
                        v___x_3257_ = v_x_3240_;
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_map_u2082_3255_);
                        lean_inc(v_map_u2081_3254_);
                        lean_dec(v_x_3240_);
                        v___x_3257_ = lean_box(0);
                        v_isShared_3258_ = v_isSharedCheck_3263_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3249_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_map_u2082_3245_, v_x_3241_, v_x_3242_);
                if v_isShared_3248_ == 0 {
                    lean_ctor_set(v___x_3247_, 1, v___x_3249_);
                    v___x_3251_ = v___x_3247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3252_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3252_, 0, v_map_u2081_3244_);
                    lean_ctor_set(v_reuseFailAlloc_3252_, 1, v___x_3249_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3252_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    lean_ctor_set(v___x_3257_, 0, v___x_3259_);
                    v___x_3261_ = v___x_3257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
                    lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_map_u2082_3255_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3262_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_d_3264_: *mut LeanObject,
    mut v_x_3265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    v_fst_3266_ = lean_ctor_get(v_x_3265_, 0);
    lean_inc(v_fst_3266_);
    v_snd_3267_ = lean_ctor_get(v_x_3265_, 1);
    lean_inc(v_snd_3267_);
    lean_dec_ref(v_x_3265_);
    v___x_3268_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_d_3264_, v_fst_3266_, v_snd_3267_);
    return v___x_3268_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    v___x_3275_ = lean_box(0);
    v___x_3276_ = lean_unsigned_to_nat(16);
    v___x_3277_ = lean_mk_array(v___x_3276_, v___x_3275_);
    return v___x_3277_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    v___x_3278_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3279_ = lean_unsigned_to_nat(0);
    v___x_3280_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3280_, 0, v___x_3279_);
    lean_ctor_set(v___x_3280_, 1, v___x_3278_);
    return v___x_3280_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    v___x_3281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3281_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    v___x_3282_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3283_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3283_, 0, v___x_3282_);
    return v___x_3283_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: u8 = 0;
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    v___x_3284_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3285_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3286_ = 1;
    v___x_3287_ = lean_alloc_ctor(0, 2, (1) as u32);
    lean_ctor_set(v___x_3287_, 0, v___x_3285_);
    lean_ctor_set(v___x_3287_, 1, v___x_3284_);
    lean_ctor_set_uint8(
        v___x_3287_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        v___x_3286_,
    );
    return v___x_3287_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___f_3288_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___f_3289_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3290_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___f_3291_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3292_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__4_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_;
    v___x_3293_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3293_, 0, v___x_3292_);
    lean_ctor_set(v___x_3293_, 1, v___f_3291_);
    lean_ctor_set(v___x_3293_, 2, v___x_3290_);
    lean_ctor_set(v___x_3293_, 3, v___f_3289_);
    lean_ctor_set(v___x_3293_, 4, v___f_3288_);
    return v___x_3293_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3295_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_);
    v___x_3296_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3295_);
    return v___x_3296_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2____boxed(
    mut v_a_3297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3298_: *mut LeanObject = core::ptr::null_mut();
    v_res_3298_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
    return v_res_3298_;
}
pub unsafe fn l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1(
    mut v_00_u03b2_3299_: *mut LeanObject,
    mut v_x_3300_: *mut LeanObject,
    mut v_x_3301_: *mut LeanObject,
    mut v_x_3302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    v___x_3303_ = l_Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1___redArg(v_x_3300_, v_x_3301_, v_x_3302_);
    return v___x_3303_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1(
    mut v_00_u03b2_3304_: *mut LeanObject,
    mut v_x_3305_: *mut LeanObject,
    mut v_x_3306_: *mut LeanObject,
    mut v_x_3307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    v___x_3308_ = l_Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1___redArg(v_x_3305_, v_x_3306_, v_x_3307_);
    return v___x_3308_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2(
    mut v_00_u03b2_3309_: *mut LeanObject,
    mut v_m_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_b_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    v___x_3313_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2___redArg(v_m_3310_, v_a_3311_, v_b_3312_);
    return v___x_3313_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_00_u03b2_3314_: *mut LeanObject,
    mut v_x_3315_: *mut LeanObject,
    mut v_x_3316_: usize,
    mut v_x_3317_: usize,
    mut v_x_3318_: *mut LeanObject,
    mut v_x_3319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg(v_x_3315_, v_x_3316_, v_x_3317_, v_x_3318_, v_x_3319_);
    return v___x_3320_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_3321_: *mut LeanObject,
    mut v_x_3322_: *mut LeanObject,
    mut v_x_3323_: *mut LeanObject,
    mut v_x_3324_: *mut LeanObject,
    mut v_x_3325_: *mut LeanObject,
    mut v_x_3326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1451__boxed_3327_: usize = 0;
    let mut v_x_1452__boxed_3328_: usize = 0;
    let mut v_res_3329_: *mut LeanObject = core::ptr::null_mut();
    v_x_1451__boxed_3327_ = lean_unbox_usize(v_x_3323_);
    lean_dec(v_x_3323_);
    v_x_1452__boxed_3328_ = lean_unbox_usize(v_x_3324_);
    lean_dec(v_x_3324_);
    v_res_3329_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_00_u03b2_3321_, v_x_3322_, v_x_1451__boxed_3327_, v_x_1452__boxed_3328_, v_x_3325_, v_x_3326_);
    return v_res_3329_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(
    mut v_00_u03b2_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_x_3332_: *mut LeanObject,
) -> u8 {
    let mut v___x_3333_: u8 = 0;
    v___x_3333_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___redArg(v_a_3331_, v_x_3332_);
    return v___x_3333_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_x_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: u8 = 0;
    let mut v_r_3338_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__4(v_00_u03b2_3334_, v_a_3335_, v_x_3336_);
    lean_dec(v_x_3336_);
    lean_dec(v_a_3335_);
    v_r_3338_ = lean_box((v_res_3337_) as usize);
    return v_r_3338_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5(
    mut v_00_u03b2_3339_: *mut LeanObject,
    mut v_data_3340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    v___x_3341_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5___redArg(v_data_3340_);
    return v___x_3341_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6(
    mut v_00_u03b2_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_b_3344_: *mut LeanObject,
    mut v_x_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    v___x_3346_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_a_3343_, v_b_3344_, v_x_3345_);
    return v___x_3346_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_3347_: *mut LeanObject,
    mut v_n_3348_: *mut LeanObject,
    mut v_k_3349_: *mut LeanObject,
    mut v_v_3350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    v___x_3351_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___redArg(v_n_3348_, v_k_3349_, v_v_3350_);
    return v___x_3351_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_3352_: *mut LeanObject,
    mut v_depth_3353_: usize,
    mut v_keys_3354_: *mut LeanObject,
    mut v_vals_3355_: *mut LeanObject,
    mut v_heq_3356_: *mut LeanObject,
    mut v_i_3357_: *mut LeanObject,
    mut v_entries_3358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    v___x_3359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___redArg(v_depth_3353_, v_keys_3354_, v_vals_3355_, v_i_3357_, v_entries_3358_);
    return v___x_3359_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_3360_: *mut LeanObject,
    mut v_depth_3361_: *mut LeanObject,
    mut v_keys_3362_: *mut LeanObject,
    mut v_vals_3363_: *mut LeanObject,
    mut v_heq_3364_: *mut LeanObject,
    mut v_i_3365_: *mut LeanObject,
    mut v_entries_3366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3367_: usize = 0;
    let mut v_res_3368_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3367_ = lean_unbox_usize(v_depth_3361_);
    lean_dec(v_depth_3361_);
    v_res_3368_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_00_u03b2_3360_, v_depth_boxed_3367_, v_keys_3362_, v_vals_3363_, v_heq_3364_, v_i_3365_, v_entries_3366_);
    lean_dec_ref(v_vals_3363_);
    lean_dec_ref(v_keys_3362_);
    return v_res_3368_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8(
    mut v_00_u03b2_3369_: *mut LeanObject,
    mut v_i_3370_: *mut LeanObject,
    mut v_source_3371_: *mut LeanObject,
    mut v_target_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    v___x_3373_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8___redArg(v_i_3370_, v_source_3371_, v_target_3372_);
    return v___x_3373_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5(
    mut v_00_u03b2_3374_: *mut LeanObject,
    mut v_x_3375_: *mut LeanObject,
    mut v_x_3376_: *mut LeanObject,
    mut v_x_3377_: *mut LeanObject,
    mut v_x_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    v___x_3379_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3_spec__5___redArg(v_x_3375_, v_x_3376_, v_x_3377_, v_x_3378_);
    return v___x_3379_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10(
    mut v_00_u03b2_3380_: *mut LeanObject,
    mut v_x_3381_: *mut LeanObject,
    mut v_x_3382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    v___x_3383_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg(v_x_3381_, v_x_3382_);
    return v___x_3383_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
    mut v_as_3384_: *mut LeanObject,
    mut v_k_3385_: *mut LeanObject,
    mut v_x_3386_: *mut LeanObject,
    mut v_x_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: u8 = 0;
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: u8 = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: u8 = 0;
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3388_ = lean_nat_add(v_x_3386_, v_x_3387_);
                v___x_3389_ = lean_unsigned_to_nat(1);
                v_m_3390_ = lean_nat_shiftr(v___x_3388_, v___x_3389_);
                lean_dec(v___x_3388_);
                v_a_3391_ = lean_array_fget_borrowed(v_as_3384_, v_m_3390_);
                v___x_3392_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_a_3391_, v_k_3385_);
                if v___x_3392_ == 0 {
                    lean_dec(v_x_3387_);
                    v___x_3393_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2__spec__1___redArg___lam__0(v_k_3385_, v_a_3391_);
                    if v___x_3393_ == 0 {
                        lean_dec(v_m_3390_);
                        lean_dec(v_x_3386_);
                        lean_inc(v_a_3391_);
                        v___x_3394_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3394_, 0, v_a_3391_);
                        return v___x_3394_;
                    } else {
                        v___x_3395_ = lean_unsigned_to_nat(0);
                        v___x_3396_ = lean_nat_dec_eq(v_m_3390_, v___x_3395_);
                        if v___x_3396_ == 0 {
                            v___x_3397_ = lean_nat_sub(v_m_3390_, v___x_3389_);
                            lean_dec(v_m_3390_);
                            v___x_3398_ = lean_nat_dec_lt(v___x_3397_, v_x_3386_);
                            if v___x_3398_ == 0 {
                                v_x_3387_ = v___x_3397_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v___x_3397_);
                                lean_dec(v_x_3386_);
                                v___x_3400_ = lean_box(0);
                                return v___x_3400_;
                            }
                        } else {
                            lean_dec(v_m_3390_);
                            lean_dec(v_x_3386_);
                            v___x_3401_ = lean_box(0);
                            return v___x_3401_;
                        }
                    }
                } else {
                    lean_dec(v_x_3386_);
                    v___x_3402_ = lean_nat_add(v_m_3390_, v___x_3389_);
                    lean_dec(v_m_3390_);
                    v___x_3403_ = lean_nat_dec_le(v___x_3402_, v_x_3387_);
                    if v___x_3403_ == 0 {
                        lean_dec(v___x_3402_);
                        lean_dec(v_x_3387_);
                        v___x_3404_ = lean_box(0);
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
    mut v_as_3406_: *mut LeanObject,
    mut v_k_3407_: *mut LeanObject,
    mut v_x_3408_: *mut LeanObject,
    mut v_x_3409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3410_: *mut LeanObject = core::ptr::null_mut();
    v_res_3410_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
        v_as_3406_, v_k_3407_, v_x_3408_, v_x_3409_,
    );
    lean_dec_ref(v_k_3407_);
    lean_dec_ref(v_as_3406_);
    return v_res_3410_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_keys_3411_: *mut LeanObject,
    mut v_vals_3412_: *mut LeanObject,
    mut v_i_3413_: *mut LeanObject,
    mut v_k_3414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: u8 = 0;
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: u8 = 0;
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3415_ = lean_array_get_size(v_keys_3411_);
                v___x_3416_ = lean_nat_dec_lt(v_i_3413_, v___x_3415_);
                if v___x_3416_ == 0 {
                    lean_dec(v_i_3413_);
                    v___x_3417_ = lean_box(0);
                    return v___x_3417_;
                } else {
                    v_k_x27_3418_ = lean_array_fget_borrowed(v_keys_3411_, v_i_3413_);
                    v___x_3419_ = lean_name_eq(v_k_3414_, v_k_x27_3418_);
                    if v___x_3419_ == 0 {
                        v___x_3420_ = lean_unsigned_to_nat(1);
                        v___x_3421_ = lean_nat_add(v_i_3413_, v___x_3420_);
                        lean_dec(v_i_3413_);
                        v_i_3413_ = v___x_3421_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3423_ = lean_array_fget_borrowed(v_vals_3412_, v_i_3413_);
                        lean_dec(v_i_3413_);
                        lean_inc(v___x_3423_);
                        v___x_3424_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3424_, 0, v___x_3423_);
                        return v___x_3424_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_keys_3425_: *mut LeanObject,
    mut v_vals_3426_: *mut LeanObject,
    mut v_i_3427_: *mut LeanObject,
    mut v_k_3428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3429_: *mut LeanObject = core::ptr::null_mut();
    v_res_3429_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3425_, v_vals_3426_, v_i_3427_, v_k_3428_);
    lean_dec(v_k_3428_);
    lean_dec_ref(v_vals_3426_);
    lean_dec_ref(v_keys_3425_);
    return v_res_3429_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(
    mut v_x_3430_: *mut LeanObject,
    mut v_x_3431_: usize,
    mut v_x_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: usize = 0;
    let mut v___x_3436_: usize = 0;
    let mut v___x_3437_: usize = 0;
    let mut v_j_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: u8 = 0;
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: usize = 0;
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3430_) == 0 {
                    v_es_3433_ = lean_ctor_get(v_x_3430_, 0);
                    v___x_3434_ = lean_box(2);
                    v___x_3435_ = 5usize;
                    v___x_3436_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__1_spec__2___redArg___closed__1);
                    v___x_3437_ = lean_usize_land(v_x_3431_, v___x_3436_);
                    v_j_3438_ = lean_usize_to_nat(v___x_3437_);
                    v___x_3439_ = lean_array_get_borrowed(v___x_3434_, v_es_3433_, v_j_3438_);
                    lean_dec(v_j_3438_);
                    match lean_obj_tag(v___x_3439_) {
                        0 => {
                            v_key_3440_ = lean_ctor_get(v___x_3439_, 0);
                            v_val_3441_ = lean_ctor_get(v___x_3439_, 1);
                            v___x_3442_ = lean_name_eq(v_x_3432_, v_key_3440_);
                            if v___x_3442_ == 0 {
                                v___x_3443_ = lean_box(0);
                                return v___x_3443_;
                            } else {
                                lean_inc(v_val_3441_);
                                v___x_3444_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3444_, 0, v_val_3441_);
                                return v___x_3444_;
                            }
                        }
                        1 => {
                            v_node_3445_ = lean_ctor_get(v___x_3439_, 0);
                            v___x_3446_ = lean_usize_shift_right(v_x_3431_, v___x_3435_);
                            v_x_3430_ = v_node_3445_;
                            v_x_3431_ = v___x_3446_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_3448_ = lean_box(0);
                            return v___x_3448_;
                        }
                    }
                } else {
                    v_ks_3449_ = lean_ctor_get(v_x_3430_, 0);
                    v_vs_3450_ = lean_ctor_get(v_x_3430_, 1);
                    v___x_3451_ = lean_unsigned_to_nat(0);
                    v___x_3452_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_ks_3449_, v_vs_3450_, v___x_3451_, v_x_3432_);
                    return v___x_3452_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_3453_: *mut LeanObject,
    mut v_x_3454_: *mut LeanObject,
    mut v_x_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_615__boxed_3456_: usize = 0;
    let mut v_res_3457_: *mut LeanObject = core::ptr::null_mut();
    v_x_615__boxed_3456_ = lean_unbox_usize(v_x_3454_);
    lean_dec(v_x_3454_);
    v_res_3457_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_3453_, v_x_615__boxed_3456_, v_x_3455_);
    lean_dec(v_x_3455_);
    lean_dec_ref(v_x_3453_);
    return v_res_3457_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(
    mut v_x_3458_: *mut LeanObject,
    mut v_x_3459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3461_: u64 = 0;
    let mut v___x_3462_: usize = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u64 = 0;
    let mut v_hash_3465_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3459_) == 0 {
                    v___x_3464_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3461_ = v___x_3464_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3465_ = lean_ctor_get_uint64(
                        v_x_3459_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_x_3466_: *mut LeanObject,
    mut v_x_3467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3468_: *mut LeanObject = core::ptr::null_mut();
    v_res_3468_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_3466_, v_x_3467_);
    lean_dec(v_x_3467_);
    lean_dec_ref(v_x_3466_);
    return v_res_3468_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(
    mut v_a_3469_: *mut LeanObject,
    mut v_x_3470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: u8 = 0;
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3470_) == 0 {
                    v___x_3471_ = lean_box(0);
                    return v___x_3471_;
                } else {
                    v_key_3472_ = lean_ctor_get(v_x_3470_, 0);
                    v_value_3473_ = lean_ctor_get(v_x_3470_, 1);
                    v_tail_3474_ = lean_ctor_get(v_x_3470_, 2);
                    v___x_3475_ = lean_name_eq(v_key_3472_, v_a_3469_);
                    if v___x_3475_ == 0 {
                        v_x_3470_ = v_tail_3474_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_3473_);
                        v___x_3477_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3477_, 0, v_value_3473_);
                        return v___x_3477_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_a_3478_: *mut LeanObject,
    mut v_x_3479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3480_: *mut LeanObject = core::ptr::null_mut();
    v_res_3480_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_3478_, v_x_3479_);
    lean_dec(v_x_3479_);
    lean_dec(v_a_3478_);
    return v_res_3480_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(
    mut v_m_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: u64 = 0;
    let mut v_hash_3501_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_3483_ = lean_ctor_get(v_m_3481_, 1);
                v___x_3484_ = lean_array_get_size(v_buckets_3483_);
                if lean_obj_tag(v_a_3482_) == 0 {
                    v___x_3500_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_SMap_insert___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2__spec__1_spec__2_spec__5_spec__8_spec__10___redArg___closed__0);
                    v___y_3486_ = v___x_3500_;
                    state = 1;
                    continue;
                } else {
                    v_hash_3501_ = lean_ctor_get_uint64(
                        v_a_3482_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3504_: *mut LeanObject = core::ptr::null_mut();
    v_res_3504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_3502_, v_a_3503_);
    lean_dec(v_a_3503_);
    lean_dec_ref(v_m_3502_);
    return v_res_3504_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
    mut v_x_3505_: *mut LeanObject,
    mut v_x_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stage_u2081_3507_: u8 = 0;
    v_stage_u2081_3507_ = lean_ctor_get_uint8(
        v_x_3505_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    if v_stage_u2081_3507_ == 0 {
        let mut v_map_u2081_3508_: *mut LeanObject = core::ptr::null_mut();
        let mut v_map_u2082_3509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_3508_ = lean_ctor_get(v_x_3505_, 0);
        v_map_u2082_3509_ = lean_ctor_get(v_x_3505_, 1);
        v___x_3510_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_map_u2082_3509_, v_x_3506_);
        if lean_obj_tag(v___x_3510_) == 0 {
            let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
            v___x_3511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_3508_, v_x_3506_);
            return v___x_3511_;
        } else {
            return v___x_3510_;
        }
    } else {
        let mut v_map_u2081_3512_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
        v_map_u2081_3512_ = lean_ctor_get(v_x_3505_, 0);
        v___x_3513_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_map_u2081_3512_, v_x_3506_);
        return v___x_3513_;
    }
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg___boxed(
    mut v_x_3514_: *mut LeanObject,
    mut v_x_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
        v_x_3514_, v_x_3515_,
    );
    lean_dec(v_x_3515_);
    lean_dec_ref(v_x_3514_);
    return v_res_3516_;
}
pub unsafe fn _init_l_Lean_getReducibilityStatusCore___closed__2() -> *mut LeanObject {
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    v___x_3519_ = l_Lean_getReducibilityStatusCore___closed__1;
    v___x_3520_ = l_Lean_getReducibilityStatusCore___closed__0;
    v___x_3521_ = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), v___x_3520_, v___x_3519_);
    return v___x_3521_;
}
pub unsafe fn lean_get_reducibility_status(
    mut v_env_3522_: *mut LeanObject,
    mut v_declName_3523_: *mut LeanObject,
) -> u8 {
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    v___x_3524_ = l_Lean_reducibilityExtraExt;
    v_ext_3525_ = lean_ctor_get(v___x_3524_, 1);
    v_toEnvExtension_3526_ = lean_ctor_get(v_ext_3525_, 0);
    v_asyncMode_3527_ = lean_ctor_get(v_toEnvExtension_3526_, 2);
    v___x_3528_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_getReducibilityStatusCore___closed__2),
        core::ptr::addr_of_mut!(l_Lean_getReducibilityStatusCore___closed__2_once),
        _init_l_Lean_getReducibilityStatusCore___closed__2,
    );
    lean_inc_ref(v_env_3522_);
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
    lean_dec(v_m_3529_);
    if lean_obj_tag(v___x_3530_) == 1 {
        let mut v_val_3531_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3532_: u8 = 0;
        lean_dec(v_declName_3523_);
        lean_dec_ref(v_env_3522_);
        v_val_3531_ = lean_ctor_get(v___x_3530_, 0);
        lean_inc(v_val_3531_);
        lean_dec_ref_known(v___x_3530_, 1);
        v___x_3532_ = (lean_unbox(v_val_3531_) as u8);
        lean_dec(v_val_3531_);
        return v___x_3532_;
    } else {
        let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_3530_);
        v___x_3533_ = lean_box(1);
        v___x_3534_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3522_, v_declName_3523_);
        if lean_obj_tag(v___x_3534_) == 0 {
            let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_3536_: *mut LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_3537_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3538_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
            v___x_3535_ = l_Lean_reducibilityCoreExt;
            v_toEnvExtension_3536_ = lean_ctor_get(v___x_3535_, 0);
            v_asyncMode_3537_ = lean_ctor_get(v_toEnvExtension_3536_, 2);
            lean_inc(v_declName_3523_);
            v___x_3538_ = l_Lean_PersistentEnvExtension_getState___redArg(
                v___x_3533_,
                v___x_3535_,
                v_env_3522_,
                v_asyncMode_3537_,
                v_declName_3523_,
            );
            v___x_3539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_3538_, v_declName_3523_);
            lean_dec(v_declName_3523_);
            lean_dec(v___x_3538_);
            if lean_obj_tag(v___x_3539_) == 0 {
                let mut v___x_3540_: u8 = 0;
                v___x_3540_ = 1;
                return v___x_3540_;
            } else {
                let mut v_val_3541_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3542_: u8 = 0;
                v_val_3541_ = lean_ctor_get(v___x_3539_, 0);
                lean_inc(v_val_3541_);
                lean_dec_ref_known(v___x_3539_, 1);
                v___x_3542_ = (lean_unbox(v_val_3541_) as u8);
                lean_dec(v_val_3541_);
                return v___x_3542_;
            }
        } else {
            let mut v_val_3543_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3545_: u8 = 0;
            let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3549_: u8 = 0;
            v_val_3543_ = lean_ctor_get(v___x_3534_, 0);
            lean_inc(v_val_3543_);
            lean_dec_ref_known(v___x_3534_, 1);
            v___x_3544_ = l_Lean_reducibilityCoreExt;
            v___x_3545_ = 0;
            v___x_3546_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                v___x_3533_,
                v___x_3544_,
                v_env_3522_,
                v_val_3543_,
                v___x_3545_,
            );
            lean_dec(v_val_3543_);
            lean_dec_ref(v_env_3522_);
            v___x_3547_ = lean_unsigned_to_nat(0);
            v___x_3548_ = lean_array_get_size(v___x_3546_);
            v___x_3549_ = lean_nat_dec_lt(v___x_3547_, v___x_3548_);
            if v___x_3549_ == 0 {
                let mut v___x_3550_: u8 = 0;
                lean_dec_ref(v___x_3546_);
                lean_dec(v_declName_3523_);
                v___x_3550_ = 1;
                return v___x_3550_;
            } else {
                let mut v___x_3551_: u8 = 0;
                let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_3554_: u8 = 0;
                v___x_3551_ = 1;
                v___x_3552_ = lean_unsigned_to_nat(1);
                v___x_3553_ = lean_nat_sub(v___x_3548_, v___x_3552_);
                v___x_3554_ = lean_nat_dec_le(v___x_3547_, v___x_3553_);
                if v___x_3554_ == 0 {
                    lean_dec(v___x_3553_);
                    lean_dec_ref(v___x_3546_);
                    lean_dec(v_declName_3523_);
                    return v___x_3551_;
                } else {
                    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
                    v___x_3555_ = lean_box((v___x_3551_) as usize);
                    v___x_3556_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3556_, 0, v_declName_3523_);
                    lean_ctor_set(v___x_3556_, 1, v___x_3555_);
                    v___x_3557_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(v___x_3546_, v___x_3556_, v___x_3547_, v___x_3553_);
                    lean_dec_ref_known(v___x_3556_, 2);
                    lean_dec_ref(v___x_3546_);
                    if lean_obj_tag(v___x_3557_) == 0 {
                        return v___x_3551_;
                    } else {
                        let mut v_val_3558_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_snd_3559_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_3560_: u8 = 0;
                        v_val_3558_ = lean_ctor_get(v___x_3557_, 0);
                        lean_inc(v_val_3558_);
                        lean_dec_ref_known(v___x_3557_, 1);
                        v_snd_3559_ = lean_ctor_get(v_val_3558_, 1);
                        lean_inc(v_snd_3559_);
                        lean_dec(v_val_3558_);
                        v___x_3560_ = (lean_unbox(v_snd_3559_) as u8);
                        lean_dec(v_snd_3559_);
                        return v___x_3560_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_getReducibilityStatusCore___boxed(
    mut v_env_3561_: *mut LeanObject,
    mut v_declName_3562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3563_: u8 = 0;
    let mut v_r_3564_: *mut LeanObject = core::ptr::null_mut();
    v_res_3563_ = lean_get_reducibility_status(v_env_3561_, v_declName_3562_);
    v_r_3564_ = lean_box((v_res_3563_) as usize);
    return v_r_3564_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(
    mut v_00_u03b2_3565_: *mut LeanObject,
    mut v_x_3566_: *mut LeanObject,
    mut v_x_3567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    v___x_3568_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___redArg(
        v_x_3566_, v_x_3567_,
    );
    return v___x_3568_;
}
pub unsafe fn l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0___boxed(
    mut v_00_u03b2_3569_: *mut LeanObject,
    mut v_x_3570_: *mut LeanObject,
    mut v_x_3571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3572_: *mut LeanObject = core::ptr::null_mut();
    v_res_3572_ = l_Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0(
        v_00_u03b2_3569_,
        v_x_3570_,
        v_x_3571_,
    );
    lean_dec(v_x_3571_);
    lean_dec_ref(v_x_3570_);
    return v_res_3572_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(
    mut v_as_3573_: *mut LeanObject,
    mut v_k_3574_: *mut LeanObject,
    mut v_x_3575_: *mut LeanObject,
    mut v_x_3576_: *mut LeanObject,
    mut v_x_3577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    v___x_3578_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___redArg(
        v_as_3573_, v_k_3574_, v_x_3575_, v_x_3576_,
    );
    return v___x_3578_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1___boxed(
    mut v_as_3579_: *mut LeanObject,
    mut v_k_3580_: *mut LeanObject,
    mut v_x_3581_: *mut LeanObject,
    mut v_x_3582_: *mut LeanObject,
    mut v_x_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3584_: *mut LeanObject = core::ptr::null_mut();
    v_res_3584_ = l_Array_binSearchAux___at___00Lean_getReducibilityStatusCore_spec__1(
        v_as_3579_, v_k_3580_, v_x_3581_, v_x_3582_, v_x_3583_,
    );
    lean_dec_ref(v_k_3580_);
    lean_dec_ref(v_as_3579_);
    return v_res_3584_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(
    mut v_00_u03b2_3585_: *mut LeanObject,
    mut v_x_3586_: *mut LeanObject,
    mut v_x_3587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    v___x_3588_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___redArg(v_x_3586_, v_x_3587_);
    return v___x_3588_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_3589_: *mut LeanObject,
    mut v_x_3590_: *mut LeanObject,
    mut v_x_3591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3592_: *mut LeanObject = core::ptr::null_mut();
    v_res_3592_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0(v_00_u03b2_3589_, v_x_3590_, v_x_3591_);
    lean_dec(v_x_3591_);
    lean_dec_ref(v_x_3590_);
    return v_res_3592_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(
    mut v_00_u03b2_3593_: *mut LeanObject,
    mut v_m_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___redArg(v_m_3594_, v_a_3595_);
    return v___x_3596_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1___boxed(
    mut v_00_u03b2_3597_: *mut LeanObject,
    mut v_m_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3600_: *mut LeanObject = core::ptr::null_mut();
    v_res_3600_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1(v_00_u03b2_3597_, v_m_3598_, v_a_3599_);
    lean_dec(v_a_3599_);
    lean_dec_ref(v_m_3598_);
    return v_res_3600_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3601_: *mut LeanObject,
    mut v_x_3602_: *mut LeanObject,
    mut v_x_3603_: usize,
    mut v_x_3604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    v___x_3605_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___redArg(v_x_3602_, v_x_3603_, v_x_3604_);
    return v___x_3605_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_3606_: *mut LeanObject,
    mut v_x_3607_: *mut LeanObject,
    mut v_x_3608_: *mut LeanObject,
    mut v_x_3609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_866__boxed_3610_: usize = 0;
    let mut v_res_3611_: *mut LeanObject = core::ptr::null_mut();
    v_x_866__boxed_3610_ = lean_unbox_usize(v_x_3608_);
    lean_dec(v_x_3608_);
    v_res_3611_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1(v_00_u03b2_3606_, v_x_3607_, v_x_866__boxed_3610_, v_x_3609_);
    lean_dec(v_x_3609_);
    lean_dec_ref(v_x_3607_);
    return v_res_3611_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3612_: *mut LeanObject,
    mut v_a_3613_: *mut LeanObject,
    mut v_x_3614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    v___x_3615_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___redArg(v_a_3613_, v_x_3614_);
    return v___x_3615_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3616_: *mut LeanObject,
    mut v_a_3617_: *mut LeanObject,
    mut v_x_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3619_: *mut LeanObject = core::ptr::null_mut();
    v_res_3619_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__1_spec__3(v_00_u03b2_3616_, v_a_3617_, v_x_3618_);
    lean_dec(v_x_3618_);
    lean_dec(v_a_3617_);
    return v_res_3619_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b2_3620_: *mut LeanObject,
    mut v_keys_3621_: *mut LeanObject,
    mut v_vals_3622_: *mut LeanObject,
    mut v_heq_3623_: *mut LeanObject,
    mut v_i_3624_: *mut LeanObject,
    mut v_k_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___redArg(v_keys_3621_, v_vals_3622_, v_i_3624_, v_k_3625_);
    return v___x_3626_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b2_3627_: *mut LeanObject,
    mut v_keys_3628_: *mut LeanObject,
    mut v_vals_3629_: *mut LeanObject,
    mut v_heq_3630_: *mut LeanObject,
    mut v_i_3631_: *mut LeanObject,
    mut v_k_3632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3633_: *mut LeanObject = core::ptr::null_mut();
    v_res_3633_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_SMap_find_x3f___at___00Lean_getReducibilityStatusCore_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3627_, v_keys_3628_, v_vals_3629_, v_heq_3630_, v_i_3631_, v_k_3632_);
    lean_dec(v_k_3632_);
    lean_dec_ref(v_vals_3629_);
    lean_dec_ref(v_keys_3628_);
    return v_res_3633_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
    mut v_env_3634_: *mut LeanObject,
    mut v_declName_3635_: *mut LeanObject,
    mut v_status_3636_: u8,
    mut v_attrKind_3637_: u8,
    mut v_currNamespace_3638_: *mut LeanObject,
) -> *mut LeanObject {
    if v_attrKind_3637_ == 0 {
        let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_currNamespace_3638_);
        v___x_3639_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3634_, v_declName_3635_);
        if lean_obj_tag(v___x_3639_) == 0 {
            let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toEnvExtension_3641_: *mut LeanObject = core::ptr::null_mut();
            let mut v_asyncMode_3642_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
            v___x_3640_ = l_Lean_reducibilityCoreExt;
            v_toEnvExtension_3641_ = lean_ctor_get(v___x_3640_, 0);
            v_asyncMode_3642_ = lean_ctor_get(v_toEnvExtension_3641_, 2);
            v___x_3643_ = lean_box((v_status_3636_) as usize);
            lean_inc(v_declName_3635_);
            v___x_3644_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3644_, 0, v_declName_3635_);
            lean_ctor_set(v___x_3644_, 1, v___x_3643_);
            v___x_3645_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                v___x_3640_,
                v_env_3634_,
                v___x_3644_,
                v_asyncMode_3642_,
                v_declName_3635_,
            );
            return v___x_3645_;
        } else {
            let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3639_, 1);
            v___x_3646_ = l_Lean_reducibilityExtraExt;
            v___x_3647_ = lean_box((v_status_3636_) as usize);
            v___x_3648_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_3648_, 0, v_declName_3635_);
            lean_ctor_set(v___x_3648_, 1, v___x_3647_);
            v___x_3649_ =
                l_Lean_ScopedEnvExtension_addEntry___redArg(v___x_3646_, v_env_3634_, v___x_3648_);
            return v___x_3649_;
        }
    } else {
        let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
        v___x_3650_ = l_Lean_reducibilityExtraExt;
        v___x_3651_ = lean_box((v_status_3636_) as usize);
        v___x_3652_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3652_, 0, v_declName_3635_);
        lean_ctor_set(v___x_3652_, 1, v___x_3651_);
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
    mut v_env_3654_: *mut LeanObject,
    mut v_declName_3655_: *mut LeanObject,
    mut v_status_3656_: *mut LeanObject,
    mut v_attrKind_3657_: *mut LeanObject,
    mut v_currNamespace_3658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_status_boxed_3659_: u8 = 0;
    let mut v_attrKind_boxed_3660_: u8 = 0;
    let mut v_res_3661_: *mut LeanObject = core::ptr::null_mut();
    v_status_boxed_3659_ = (lean_unbox(v_status_3656_) as u8);
    v_attrKind_boxed_3660_ = (lean_unbox(v_attrKind_3657_) as u8);
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
    mut v_env_3662_: *mut LeanObject,
    mut v_declName_3663_: *mut LeanObject,
    mut v_status_3664_: u8,
) -> *mut LeanObject {
    let mut v___x_3665_: u8 = 0;
    let mut v___x_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = 0;
    v___x_3666_ = lean_box(0);
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
    mut v_env_3668_: *mut LeanObject,
    mut v_declName_3669_: *mut LeanObject,
    mut v_status_3670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_status_boxed_3671_: u8 = 0;
    let mut v_res_3672_: *mut LeanObject = core::ptr::null_mut();
    v_status_boxed_3671_ = (lean_unbox(v_status_3670_) as u8);
    v_res_3672_ = lean_set_reducibility_status(v_env_3668_, v_declName_3669_, v_status_boxed_3671_);
    return v_res_3672_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(
    mut v_name_3673_: *mut LeanObject,
    mut v_decl_3674_: *mut LeanObject,
    mut v_ref_3675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3691_: u8 = 0;
    let mut v_unused_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3677_ = lean_ctor_get(v_decl_3674_, 0);
                v_descr_3678_ = lean_ctor_get(v_decl_3674_, 1);
                v_deprecation_x3f_3679_ = lean_ctor_get(v_decl_3674_, 2);
                v___x_3680_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3681_ = (lean_unbox(v_defValue_3677_) as u8);
                lean_ctor_set_uint8(v___x_3680_, 0 as u32, v___x_3681_);
                lean_inc(v_deprecation_x3f_3679_);
                lean_inc_ref(v_descr_3678_);
                lean_inc_n(v_name_3673_, 2);
                v___x_3682_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3682_, 0, v_name_3673_);
                lean_ctor_set(v___x_3682_, 1, v_ref_3675_);
                lean_ctor_set(v___x_3682_, 2, v___x_3680_);
                lean_ctor_set(v___x_3682_, 3, v_descr_3678_);
                lean_ctor_set(v___x_3682_, 4, v_deprecation_x3f_3679_);
                v___x_3683_ = lean_register_option(v_name_3673_, v___x_3682_);
                if lean_obj_tag(v___x_3683_) == 0 {
                    v_isSharedCheck_3691_ = (!lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3691_ == 0 {
                        v_unused_3692_ = lean_ctor_get(v___x_3683_, 0);
                        lean_dec(v_unused_3692_);
                        v___x_3685_ = v___x_3683_;
                        v_isShared_3686_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3683_);
                        v___x_3685_ = lean_box(0);
                        v_isShared_3686_ = v_isSharedCheck_3691_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3673_);
                    v_a_3693_ = lean_ctor_get(v___x_3683_, 0);
                    v_isSharedCheck_3700_ = (!lean_is_exclusive(v___x_3683_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v___x_3695_ = v___x_3683_;
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3693_);
                        lean_dec(v___x_3683_);
                        v___x_3695_ = lean_box(0);
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_3677_);
                v___x_3687_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3687_, 0, v_name_3673_);
                lean_ctor_set(v___x_3687_, 1, v_defValue_3677_);
                if v_isShared_3686_ == 0 {
                    lean_ctor_set(v___x_3685_, 0, v___x_3687_);
                    v___x_3689_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3687_);
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
                    v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
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
    mut v_name_3701_: *mut LeanObject,
    mut v_decl_3702_: *mut LeanObject,
    mut v_ref_3703_: *mut LeanObject,
    mut v_a_3704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3705_: *mut LeanObject = core::ptr::null_mut();
    v_res_3705_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v_name_3701_, v_decl_3702_, v_ref_3703_);
    lean_dec_ref(v_decl_3702_);
    return v_res_3705_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    v___x_3720_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3721_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3722_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_;
    v___x_3723_ = l_Lean_Option_register___at___00__private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4__spec__0(v___x_3720_, v___x_3721_, v___x_3722_);
    return v___x_3723_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4____boxed(
    mut v_a_3724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3725_: *mut LeanObject = core::ptr::null_mut();
    v_res_3725_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
    return v_res_3725_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(
    mut v_opts_3726_: *mut LeanObject,
    mut v_opt_3727_: *mut LeanObject,
) -> u8 {
    let mut v_name_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    v_name_3728_ = lean_ctor_get(v_opt_3727_, 0);
    v_defValue_3729_ = lean_ctor_get(v_opt_3727_, 1);
    v_map_3730_ = lean_ctor_get(v_opts_3726_, 0);
    v___x_3731_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3730_,
            v_name_3728_,
        );
    if lean_obj_tag(v___x_3731_) == 0 {
        let mut v___x_3732_: u8 = 0;
        v___x_3732_ = (lean_unbox(v_defValue_3729_) as u8);
        return v___x_3732_;
    } else {
        let mut v_val_3733_: *mut LeanObject = core::ptr::null_mut();
        v_val_3733_ = lean_ctor_get(v___x_3731_, 0);
        lean_inc(v_val_3733_);
        lean_dec_ref_known(v___x_3731_, 1);
        if lean_obj_tag(v_val_3733_) == 1 {
            let mut v_v_3734_: u8 = 0;
            v_v_3734_ = lean_ctor_get_uint8(v_val_3733_, 0 as u32);
            lean_dec_ref_known(v_val_3733_, 0);
            return v_v_3734_;
        } else {
            let mut v___x_3735_: u8 = 0;
            lean_dec(v_val_3733_);
            v___x_3735_ = (lean_unbox(v_defValue_3729_) as u8);
            return v___x_3735_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0___boxed(
    mut v_opts_3736_: *mut LeanObject,
    mut v_opt_3737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3738_: u8 = 0;
    let mut v_r_3739_: *mut LeanObject = core::ptr::null_mut();
    v_res_3738_ =
        l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(
            v_opts_3736_,
            v_opt_3737_,
        );
    lean_dec_ref(v_opt_3737_);
    lean_dec_ref(v_opts_3736_);
    v_r_3739_ = lean_box((v_res_3738_) as usize);
    return v_r_3739_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    v___x_3740_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3740_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1()
-> *mut LeanObject {
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    v___x_3741_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__0);
    v___x_3742_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3742_, 0, v___x_3741_);
    return v___x_3742_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2()
-> *mut LeanObject {
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    v___x_3743_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
    v___x_3744_ = lean_unsigned_to_nat(0);
    v___x_3745_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_3745_, 0, v___x_3744_);
    lean_ctor_set(v___x_3745_, 1, v___x_3744_);
    lean_ctor_set(v___x_3745_, 2, v___x_3744_);
    lean_ctor_set(v___x_3745_, 3, v___x_3744_);
    lean_ctor_set(v___x_3745_, 4, v___x_3743_);
    lean_ctor_set(v___x_3745_, 5, v___x_3743_);
    lean_ctor_set(v___x_3745_, 6, v___x_3743_);
    lean_ctor_set(v___x_3745_, 7, v___x_3743_);
    lean_ctor_set(v___x_3745_, 8, v___x_3743_);
    lean_ctor_set(v___x_3745_, 9, v___x_3743_);
    return v___x_3745_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3()
-> *mut LeanObject {
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    v___x_3746_ = lean_unsigned_to_nat(32);
    v___x_3747_ = lean_mk_empty_array_with_capacity(v___x_3746_);
    v___x_3748_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3748_, 0, v___x_3747_);
    return v___x_3748_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_3749_: usize = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    v___x_3749_ = 5usize;
    v___x_3750_ = lean_unsigned_to_nat(0);
    v___x_3751_ = lean_unsigned_to_nat(32);
    v___x_3752_ = lean_mk_empty_array_with_capacity(v___x_3751_);
    v___x_3753_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__3);
    v___x_3754_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_3754_, 0, v___x_3753_);
    lean_ctor_set(v___x_3754_, 1, v___x_3752_);
    lean_ctor_set(v___x_3754_, 2, v___x_3750_);
    lean_ctor_set(v___x_3754_, 3, v___x_3750_);
    lean_ctor_set_usize(v___x_3754_, 4, v___x_3749_);
    return v___x_3754_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5()
-> *mut LeanObject {
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    v___x_3755_ = lean_box(1);
    v___x_3756_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__4);
    v___x_3757_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__1);
    v___x_3758_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_3758_, 0, v___x_3757_);
    lean_ctor_set(v___x_3758_, 1, v___x_3756_);
    lean_ctor_set(v___x_3758_, 2, v___x_3755_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(
    mut v_msgData_3759_: *mut LeanObject,
    mut v___y_3760_: *mut LeanObject,
    mut v___y_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    v___x_3763_ = lean_st_ref_get(v___y_3761_);
    v_env_3764_ = lean_ctor_get(v___x_3763_, 0);
    lean_inc_ref(v_env_3764_);
    lean_dec(v___x_3763_);
    v_options_3765_ = lean_ctor_get(v___y_3760_, 2);
    v___x_3766_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
    v___x_3767_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
    lean_inc_ref(v_options_3765_);
    v___x_3768_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_3768_, 0, v_env_3764_);
    lean_ctor_set(v___x_3768_, 1, v___x_3766_);
    lean_ctor_set(v___x_3768_, 2, v___x_3767_);
    lean_ctor_set(v___x_3768_, 3, v_options_3765_);
    v___x_3769_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_3769_, 0, v___x_3768_);
    lean_ctor_set(v___x_3769_, 1, v_msgData_3759_);
    v___x_3770_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3770_, 0, v___x_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___boxed(
    mut v_msgData_3771_: *mut LeanObject,
    mut v___y_3772_: *mut LeanObject,
    mut v___y_3773_: *mut LeanObject,
    mut v___y_3774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3775_: *mut LeanObject = core::ptr::null_mut();
    v_res_3775_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msgData_3771_, v___y_3772_, v___y_3773_);
    lean_dec(v___y_3773_);
    lean_dec_ref(v___y_3772_);
    return v_res_3775_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(
    mut v_msg_3776_: *mut LeanObject,
    mut v___y_3777_: *mut LeanObject,
    mut v___y_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3785_: u8 = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3780_ = lean_ctor_get(v___y_3777_, 5);
                v___x_3781_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1(v_msg_3776_, v___y_3777_, v___y_3778_);
                v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
                v_isSharedCheck_3790_ = (!lean_is_exclusive(v___x_3781_)) as u8;
                if v_isSharedCheck_3790_ == 0 {
                    v___x_3784_ = v___x_3781_;
                    v_isShared_3785_ = v_isSharedCheck_3790_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3782_);
                    lean_dec(v___x_3781_);
                    v___x_3784_ = lean_box(0);
                    v_isShared_3785_ = v_isSharedCheck_3790_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3780_);
                v___x_3786_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3786_, 0, v_ref_3780_);
                lean_ctor_set(v___x_3786_, 1, v_a_3782_);
                if v_isShared_3785_ == 0 {
                    lean_ctor_set_tag(v___x_3784_, 1);
                    lean_ctor_set(v___x_3784_, 0, v___x_3786_);
                    v___x_3788_ = v___x_3784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
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
    mut v_msg_3791_: *mut LeanObject,
    mut v___y_3792_: *mut LeanObject,
    mut v___y_3793_: *mut LeanObject,
    mut v___y_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3795_: *mut LeanObject = core::ptr::null_mut();
    v_res_3795_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_3791_, v___y_3792_, v___y_3793_);
    lean_dec(v___y_3793_);
    lean_dec_ref(v___y_3792_);
    return v_res_3795_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(
    mut v_ref_3796_: *mut LeanObject,
    mut v_msg_3797_: *mut LeanObject,
    mut v___y_3798_: *mut LeanObject,
    mut v___y_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3813_: u8 = 0;
    let mut v_cancelTk_x3f_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3815_: u8 = 0;
    let mut v_inheritedTraceOptions_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_3801_ = lean_ctor_get(v___y_3798_, 0);
    v_fileMap_3802_ = lean_ctor_get(v___y_3798_, 1);
    v_options_3803_ = lean_ctor_get(v___y_3798_, 2);
    v_currRecDepth_3804_ = lean_ctor_get(v___y_3798_, 3);
    v_maxRecDepth_3805_ = lean_ctor_get(v___y_3798_, 4);
    v_ref_3806_ = lean_ctor_get(v___y_3798_, 5);
    v_currNamespace_3807_ = lean_ctor_get(v___y_3798_, 6);
    v_openDecls_3808_ = lean_ctor_get(v___y_3798_, 7);
    v_initHeartbeats_3809_ = lean_ctor_get(v___y_3798_, 8);
    v_maxHeartbeats_3810_ = lean_ctor_get(v___y_3798_, 9);
    v_quotContext_3811_ = lean_ctor_get(v___y_3798_, 10);
    v_currMacroScope_3812_ = lean_ctor_get(v___y_3798_, 11);
    v_diag_3813_ = lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3814_ = lean_ctor_get(v___y_3798_, 12);
    v_suppressElabErrors_3815_ = lean_ctor_get_uint8(
        v___y_3798_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3816_ = lean_ctor_get(v___y_3798_, 13);
    v_ref_3817_ = l_Lean_replaceRef(v_ref_3796_, v_ref_3806_);
    lean_inc_ref(v_inheritedTraceOptions_3816_);
    lean_inc(v_cancelTk_x3f_3814_);
    lean_inc(v_currMacroScope_3812_);
    lean_inc(v_quotContext_3811_);
    lean_inc(v_maxHeartbeats_3810_);
    lean_inc(v_initHeartbeats_3809_);
    lean_inc(v_openDecls_3808_);
    lean_inc(v_currNamespace_3807_);
    lean_inc(v_maxRecDepth_3805_);
    lean_inc(v_currRecDepth_3804_);
    lean_inc_ref(v_options_3803_);
    lean_inc_ref(v_fileMap_3802_);
    lean_inc_ref(v_fileName_3801_);
    v___x_3818_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_3818_, 0, v_fileName_3801_);
    lean_ctor_set(v___x_3818_, 1, v_fileMap_3802_);
    lean_ctor_set(v___x_3818_, 2, v_options_3803_);
    lean_ctor_set(v___x_3818_, 3, v_currRecDepth_3804_);
    lean_ctor_set(v___x_3818_, 4, v_maxRecDepth_3805_);
    lean_ctor_set(v___x_3818_, 5, v_ref_3817_);
    lean_ctor_set(v___x_3818_, 6, v_currNamespace_3807_);
    lean_ctor_set(v___x_3818_, 7, v_openDecls_3808_);
    lean_ctor_set(v___x_3818_, 8, v_initHeartbeats_3809_);
    lean_ctor_set(v___x_3818_, 9, v_maxHeartbeats_3810_);
    lean_ctor_set(v___x_3818_, 10, v_quotContext_3811_);
    lean_ctor_set(v___x_3818_, 11, v_currMacroScope_3812_);
    lean_ctor_set(v___x_3818_, 12, v_cancelTk_x3f_3814_);
    lean_ctor_set(v___x_3818_, 13, v_inheritedTraceOptions_3816_);
    lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_3813_,
    );
    lean_ctor_set_uint8(
        v___x_3818_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3815_,
    );
    v___x_3819_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_3797_, v___x_3818_, v___y_3799_);
    lean_dec_ref_known(v___x_3818_, 14);
    return v___x_3819_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg___boxed(
    mut v_ref_3820_: *mut LeanObject,
    mut v_msg_3821_: *mut LeanObject,
    mut v___y_3822_: *mut LeanObject,
    mut v___y_3823_: *mut LeanObject,
    mut v___y_3824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3825_: *mut LeanObject = core::ptr::null_mut();
    v_res_3825_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3820_, v_msg_3821_, v___y_3822_, v___y_3823_);
    lean_dec(v___y_3823_);
    lean_dec_ref(v___y_3822_);
    lean_dec(v_ref_3820_);
    return v_res_3825_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    v___x_3827_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__0;
    v___x_3828_ = l_Lean_stringToMessageData(v___x_3827_);
    return v___x_3828_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__2;
    v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
    return v___x_3831_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__4;
    v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
    return v___x_3834_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
    return v___x_3837_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    v___x_3839_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_3840_ = l_Lean_stringToMessageData(v___x_3839_);
    return v___x_3840_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    v___x_3842_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_3843_ = l_Lean_stringToMessageData(v___x_3842_);
    return v___x_3843_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    v___x_3845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_3846_ = l_Lean_stringToMessageData(v___x_3845_);
    return v___x_3846_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(
    mut v_msg_3847_: *mut LeanObject,
    mut v_declHint_3848_: *mut LeanObject,
    mut v___y_3849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: u8 = 0;
    let mut v_isExporting_3854_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: u8 = 0;
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3851_ = lean_st_ref_get(v___y_3849_);
                v_env_3852_ = lean_ctor_get(v___x_3851_, 0);
                lean_inc_ref(v_env_3852_);
                lean_dec(v___x_3851_);
                v___x_3853_ = l_Lean_Name_isAnonymous(v_declHint_3848_);
                if v___x_3853_ == 0 {
                    v_isExporting_3854_ = lean_ctor_get_uint8(
                        v_env_3852_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_3854_ == 0 {
                        lean_dec_ref(v_env_3852_);
                        lean_dec(v_declHint_3848_);
                        v___x_3855_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3855_, 0, v_msg_3847_);
                        return v___x_3855_;
                    } else {
                        lean_inc_ref(v_env_3852_);
                        v___x_3856_ = l_Lean_Environment_setExporting(v_env_3852_, v___x_3853_);
                        lean_inc(v_declHint_3848_);
                        lean_inc_ref(v___x_3856_);
                        v___x_3857_ = l_Lean_Environment_contains(
                            v___x_3856_,
                            v_declHint_3848_,
                            v_isExporting_3854_,
                        );
                        if v___x_3857_ == 0 {
                            lean_dec_ref(v___x_3856_);
                            lean_dec_ref(v_env_3852_);
                            lean_dec(v_declHint_3848_);
                            v___x_3858_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_3858_, 0, v_msg_3847_);
                            return v___x_3858_;
                        } else {
                            v___x_3859_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__2);
                            v___x_3860_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1_spec__1___closed__5);
                            v___x_3861_ = l_Lean_Options_empty;
                            v___x_3862_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_3862_, 0, v___x_3856_);
                            lean_ctor_set(v___x_3862_, 1, v___x_3859_);
                            lean_ctor_set(v___x_3862_, 2, v___x_3860_);
                            lean_ctor_set(v___x_3862_, 3, v___x_3861_);
                            lean_inc(v_declHint_3848_);
                            v___x_3863_ =
                                l_Lean_MessageData_ofConstName(v_declHint_3848_, v___x_3853_);
                            v_c_3864_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_3864_, 0, v___x_3862_);
                            lean_ctor_set(v_c_3864_, 1, v___x_3863_);
                            v___x_3865_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_3852_,
                                v_declHint_3848_,
                            );
                            if lean_obj_tag(v___x_3865_) == 0 {
                                lean_dec_ref(v_env_3852_);
                                lean_dec(v_declHint_3848_);
                                v___x_3866_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                                v___x_3867_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3867_, 0, v___x_3866_);
                                lean_ctor_set(v___x_3867_, 1, v_c_3864_);
                                v___x_3868_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__3);
                                v___x_3869_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3869_, 0, v___x_3867_);
                                lean_ctor_set(v___x_3869_, 1, v___x_3868_);
                                v___x_3870_ = l_Lean_MessageData_note(v___x_3869_);
                                v___x_3871_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_3871_, 0, v_msg_3847_);
                                lean_ctor_set(v___x_3871_, 1, v___x_3870_);
                                v___x_3872_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3872_, 0, v___x_3871_);
                                return v___x_3872_;
                            } else {
                                v_val_3873_ = lean_ctor_get(v___x_3865_, 0);
                                v_isSharedCheck_3908_ = (!lean_is_exclusive(v___x_3865_)) as u8;
                                if v_isSharedCheck_3908_ == 0 {
                                    v___x_3875_ = v___x_3865_;
                                    v_isShared_3876_ = v_isSharedCheck_3908_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_3873_);
                                    lean_dec(v___x_3865_);
                                    v___x_3875_ = lean_box(0);
                                    v_isShared_3876_ = v_isSharedCheck_3908_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_3852_);
                    lean_dec(v_declHint_3848_);
                    v___x_3909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3909_, 0, v_msg_3847_);
                    return v___x_3909_;
                }
            }
            1 => {
                v___x_3877_ = lean_box(0);
                v___x_3878_ = l_Lean_Environment_header(v_env_3852_);
                lean_dec_ref(v_env_3852_);
                v___x_3879_ = l_Lean_EnvironmentHeader_moduleNames(v___x_3878_);
                v_mod_3880_ = lean_array_get(v___x_3877_, v___x_3879_, v_val_3873_);
                lean_dec(v_val_3873_);
                lean_dec_ref(v___x_3879_);
                v___x_3881_ = l_Lean_isPrivateName(v_declHint_3848_);
                lean_dec(v_declHint_3848_);
                if v___x_3881_ == 0 {
                    v___x_3882_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__5);
                    v___x_3883_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3883_, 0, v___x_3882_);
                    lean_ctor_set(v___x_3883_, 1, v_c_3864_);
                    v___x_3884_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_3885_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3885_, 0, v___x_3883_);
                    lean_ctor_set(v___x_3885_, 1, v___x_3884_);
                    v___x_3886_ = l_Lean_MessageData_ofName(v_mod_3880_);
                    v___x_3887_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3887_, 0, v___x_3885_);
                    lean_ctor_set(v___x_3887_, 1, v___x_3886_);
                    v___x_3888_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__9);
                    v___x_3889_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3889_, 0, v___x_3887_);
                    lean_ctor_set(v___x_3889_, 1, v___x_3888_);
                    v___x_3890_ = l_Lean_MessageData_note(v___x_3889_);
                    v___x_3891_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3891_, 0, v_msg_3847_);
                    lean_ctor_set(v___x_3891_, 1, v___x_3890_);
                    if v_isShared_3876_ == 0 {
                        lean_ctor_set_tag(v___x_3875_, 0);
                        lean_ctor_set(v___x_3875_, 0, v___x_3891_);
                        v___x_3893_ = v___x_3875_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
                        v___x_3893_ = v_reuseFailAlloc_3894_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3895_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__1);
                    v___x_3896_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                    lean_ctor_set(v___x_3896_, 1, v_c_3864_);
                    v___x_3897_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_3898_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3898_, 0, v___x_3896_);
                    lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                    v___x_3899_ = l_Lean_MessageData_ofName(v_mod_3880_);
                    v___x_3900_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3900_, 0, v___x_3898_);
                    lean_ctor_set(v___x_3900_, 1, v___x_3899_);
                    v___x_3901_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_3902_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3902_, 0, v___x_3900_);
                    lean_ctor_set(v___x_3902_, 1, v___x_3901_);
                    v___x_3903_ = l_Lean_MessageData_note(v___x_3902_);
                    v___x_3904_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_3904_, 0, v_msg_3847_);
                    lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                    if v_isShared_3876_ == 0 {
                        lean_ctor_set_tag(v___x_3875_, 0);
                        lean_ctor_set(v___x_3875_, 0, v___x_3904_);
                        v___x_3906_ = v___x_3875_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
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
    mut v_msg_3910_: *mut LeanObject,
    mut v_declHint_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3914_: *mut LeanObject = core::ptr::null_mut();
    v_res_3914_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3910_, v_declHint_3911_, v___y_3912_);
    lean_dec(v___y_3912_);
    return v_res_3914_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(
    mut v_msg_3915_: *mut LeanObject,
    mut v_declHint_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
    mut v___y_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3924_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_3915_, v_declHint_3916_, v___y_3918_);
                v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
                v_isSharedCheck_3930_ = (!lean_is_exclusive(v___x_3920_)) as u8;
                if v_isSharedCheck_3930_ == 0 {
                    v___x_3923_ = v___x_3920_;
                    v_isShared_3924_ = v_isSharedCheck_3930_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3921_);
                    lean_dec(v___x_3920_);
                    v___x_3923_ = lean_box(0);
                    v_isShared_3924_ = v_isSharedCheck_3930_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3925_ = l_Lean_unknownIdentifierMessageTag;
                v___x_3926_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_3926_, 0, v___x_3925_);
                lean_ctor_set(v___x_3926_, 1, v_a_3921_);
                if v_isShared_3924_ == 0 {
                    lean_ctor_set(v___x_3923_, 0, v___x_3926_);
                    v___x_3928_ = v___x_3923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
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
    mut v_msg_3931_: *mut LeanObject,
    mut v_declHint_3932_: *mut LeanObject,
    mut v___y_3933_: *mut LeanObject,
    mut v___y_3934_: *mut LeanObject,
    mut v___y_3935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3936_: *mut LeanObject = core::ptr::null_mut();
    v_res_3936_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3931_, v_declHint_3932_, v___y_3933_, v___y_3934_);
    lean_dec(v___y_3934_);
    lean_dec_ref(v___y_3933_);
    return v_res_3936_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(
    mut v_ref_3937_: *mut LeanObject,
    mut v_msg_3938_: *mut LeanObject,
    mut v_declHint_3939_: *mut LeanObject,
    mut v___y_3940_: *mut LeanObject,
    mut v___y_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    v___x_3943_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8(v_msg_3938_, v_declHint_3939_, v___y_3940_, v___y_3941_);
    v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
    lean_inc(v_a_3944_);
    lean_dec_ref(v___x_3943_);
    v___x_3945_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_3937_, v_a_3944_, v___y_3940_, v___y_3941_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg___boxed(
    mut v_ref_3946_: *mut LeanObject,
    mut v_msg_3947_: *mut LeanObject,
    mut v_declHint_3948_: *mut LeanObject,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3952_: *mut LeanObject = core::ptr::null_mut();
    v_res_3952_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3946_, v_msg_3947_, v_declHint_3948_, v___y_3949_, v___y_3950_);
    lean_dec(v___y_3950_);
    lean_dec_ref(v___y_3949_);
    lean_dec(v_ref_3946_);
    return v_res_3952_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    v___x_3954_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_3955_ = l_Lean_stringToMessageData(v___x_3954_);
    return v___x_3955_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_3958_ = l_Lean_stringToMessageData(v___x_3957_);
    return v___x_3958_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(
    mut v_ref_3959_: *mut LeanObject,
    mut v_constName_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    v___x_3964_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_3965_ = 0;
    lean_inc(v_constName_3960_);
    v___x_3966_ = l_Lean_MessageData_ofConstName(v_constName_3960_, v___x_3965_);
    v___x_3967_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3967_, 0, v___x_3964_);
    lean_ctor_set(v___x_3967_, 1, v___x_3966_);
    v___x_3968_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_3969_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_3969_, 0, v___x_3967_);
    lean_ctor_set(v___x_3969_, 1, v___x_3968_);
    v___x_3970_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_3959_, v___x_3969_, v_constName_3960_, v___y_3961_, v___y_3962_);
    return v___x_3970_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_ref_3971_: *mut LeanObject,
    mut v_constName_3972_: *mut LeanObject,
    mut v___y_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
    mut v___y_3975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3976_: *mut LeanObject = core::ptr::null_mut();
    v_res_3976_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_3971_, v_constName_3972_, v___y_3973_, v___y_3974_);
    lean_dec(v___y_3974_);
    lean_dec_ref(v___y_3973_);
    lean_dec(v_ref_3971_);
    return v_res_3976_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(
    mut v_constName_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    v_ref_3981_ = lean_ctor_get(v___y_3978_, 5);
    v___x_3982_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_3981_, v_constName_3977_, v___y_3978_, v___y_3979_);
    return v___x_3982_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg___boxed(
    mut v_constName_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3987_: *mut LeanObject = core::ptr::null_mut();
    v_res_3987_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_3983_, v___y_3984_, v___y_3985_);
    lean_dec(v___y_3985_);
    lean_dec_ref(v___y_3984_);
    return v_res_3987_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(
    mut v_constName_3988_: *mut LeanObject,
    mut v___y_3989_: *mut LeanObject,
    mut v___y_3990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: u8 = 0;
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4000_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4004_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3992_ = lean_st_ref_get(v___y_3990_);
                v_env_3993_ = lean_ctor_get(v___x_3992_, 0);
                lean_inc_ref(v_env_3993_);
                lean_dec(v___x_3992_);
                v___x_3994_ = 0;
                lean_inc(v_constName_3988_);
                v___x_3995_ =
                    l_Lean_Environment_find_x3f(v_env_3993_, v_constName_3988_, v___x_3994_);
                if lean_obj_tag(v___x_3995_) == 0 {
                    v___x_3996_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_3988_, v___y_3989_, v___y_3990_);
                    return v___x_3996_;
                } else {
                    lean_dec(v_constName_3988_);
                    v_val_3997_ = lean_ctor_get(v___x_3995_, 0);
                    v_isSharedCheck_4004_ = (!lean_is_exclusive(v___x_3995_)) as u8;
                    if v_isSharedCheck_4004_ == 0 {
                        v___x_3999_ = v___x_3995_;
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3997_);
                        lean_dec(v___x_3995_);
                        v___x_3999_ = lean_box(0);
                        v_isShared_4000_ = v_isSharedCheck_4004_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4000_ == 0 {
                    lean_ctor_set_tag(v___x_3999_, 0);
                    v___x_4002_ = v___x_3999_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_val_3997_);
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
    mut v_constName_4005_: *mut LeanObject,
    mut v___y_4006_: *mut LeanObject,
    mut v___y_4007_: *mut LeanObject,
    mut v___y_4008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4009_: *mut LeanObject = core::ptr::null_mut();
    v_res_4009_ =
        l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(
            v_constName_4005_,
            v___y_4006_,
            v___y_4007_,
        );
    lean_dec(v___y_4007_);
    lean_dec_ref(v___y_4006_);
    return v_res_4009_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    v___x_4011_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__0;
    v___x_4012_ = l_Lean_stringToMessageData(v___x_4011_);
    return v___x_4012_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__2;
    v___x_4015_ = l_Lean_stringToMessageData(v___x_4014_);
    return v___x_4015_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    v___x_4017_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__4;
    v___x_4018_ = l_Lean_stringToMessageData(v___x_4017_);
    return v___x_4018_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    v___x_4020_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__6;
    v___x_4021_ = l_Lean_stringToMessageData(v___x_4020_);
    return v___x_4021_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    v___x_4023_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__8;
    v___x_4024_ = l_Lean_stringToMessageData(v___x_4023_);
    return v___x_4024_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11()
-> *mut LeanObject {
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    v___x_4026_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__10;
    v___x_4027_ = l_Lean_stringToMessageData(v___x_4026_);
    return v___x_4027_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    v___x_4029_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__12;
    v___x_4030_ = l_Lean_stringToMessageData(v___x_4029_);
    return v___x_4030_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    v___x_4032_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__14;
    v___x_4033_ = l_Lean_stringToMessageData(v___x_4032_);
    return v___x_4033_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    v___x_4035_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__16;
    v___x_4036_ = l_Lean_stringToMessageData(v___x_4035_);
    return v___x_4036_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19()
-> *mut LeanObject {
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    v___x_4038_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__18;
    v___x_4039_ = l_Lean_stringToMessageData(v___x_4038_);
    return v___x_4039_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21()
-> *mut LeanObject {
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    v___x_4041_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__20;
    v___x_4042_ = l_Lean_stringToMessageData(v___x_4041_);
    return v___x_4042_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23()
-> *mut LeanObject {
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    v___x_4044_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__22;
    v___x_4045_ = l_Lean_stringToMessageData(v___x_4044_);
    return v___x_4045_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25()
-> *mut LeanObject {
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    v___x_4047_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__24;
    v___x_4048_ = l_Lean_stringToMessageData(v___x_4047_);
    return v___x_4048_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27()
-> *mut LeanObject {
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    v___x_4050_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__26;
    v___x_4051_ = l_Lean_stringToMessageData(v___x_4050_);
    return v___x_4051_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29()
-> *mut LeanObject {
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    v___x_4053_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__28;
    v___x_4054_ = l_Lean_stringToMessageData(v___x_4053_);
    return v___x_4054_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31()
-> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__30;
    v___x_4057_ = l_Lean_stringToMessageData(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33()
-> *mut LeanObject {
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    v___x_4059_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__32;
    v___x_4060_ = l_Lean_stringToMessageData(v___x_4059_);
    return v___x_4060_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35()
-> *mut LeanObject {
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    v___x_4062_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__34;
    v___x_4063_ = l_Lean_stringToMessageData(v___x_4062_);
    return v___x_4063_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37()
-> *mut LeanObject {
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    v___x_4065_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__36;
    v___x_4066_ = l_Lean_stringToMessageData(v___x_4065_);
    return v___x_4066_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39()
-> *mut LeanObject {
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    v___x_4068_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__38;
    v___x_4069_ = l_Lean_stringToMessageData(v___x_4068_);
    return v___x_4069_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41()
-> *mut LeanObject {
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    v___x_4071_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__40;
    v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
    return v___x_4072_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(
    mut v_declName_4073_: *mut LeanObject,
    mut v_status_4074_: u8,
    mut v_suffix_4075_: *mut LeanObject,
    mut v_attrKind_4076_: u8,
    mut v___y_4077_: *mut LeanObject,
    mut v___y_4078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: u8 = 0;
    let mut v___y_4102_: u8 = 0;
    let mut v___y_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4150_: u8 = 0;
    let mut v___y_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: u8 = 0;
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4098_ = lean_ctor_get(v___y_4077_, 2);
                v___x_4099_ = l_Lean_allowUnsafeReducibility;
                v___x_4100_ = l_Lean_Option_get___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__0(v_options_4098_, v___x_4099_);
                if v___x_4100_ == 0 {
                    lean_inc(v_declName_4073_);
                    v___x_4218_ = l_Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2(v_declName_4073_, v___y_4077_, v___y_4078_);
                    if lean_obj_tag(v___x_4218_) == 0 {
                        v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
                        lean_inc(v_a_4219_);
                        lean_dec_ref_known(v___x_4218_, 1);
                        v___x_4220_ = l_Lean_ConstantInfo_isDefinition(v_a_4219_);
                        lean_dec(v_a_4219_);
                        if v___x_4220_ == 0 {
                            v___x_4221_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
                            v___x_4222_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4220_);
                            v___x_4223_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4223_, 0, v___x_4221_);
                            lean_ctor_set(v___x_4223_, 1, v___x_4222_);
                            v___x_4224_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__41);
                            v___x_4225_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4225_, 0, v___x_4223_);
                            lean_ctor_set(v___x_4225_, 1, v___x_4224_);
                            v___x_4226_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4226_, 0, v___x_4225_);
                            lean_ctor_set(v___x_4226_, 1, v_suffix_4075_);
                            v___x_4227_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4226_, v___y_4077_, v___y_4078_);
                            return v___x_4227_;
                        } else {
                            v___y_4160_ = v___y_4077_;
                            v___y_4161_ = v___y_4078_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_suffix_4075_);
                        lean_dec(v_declName_4073_);
                        v_a_4228_ = lean_ctor_get(v___x_4218_, 0);
                        v_isSharedCheck_4235_ = (!lean_is_exclusive(v___x_4218_)) as u8;
                        if v_isSharedCheck_4235_ == 0 {
                            v___x_4230_ = v___x_4218_;
                            v_isShared_4231_ = v_isSharedCheck_4235_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4228_);
                            lean_dec(v___x_4218_);
                            v___x_4230_ = lean_box(0);
                            v_isShared_4231_ = v_isSharedCheck_4235_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_suffix_4075_);
                    lean_dec(v_declName_4073_);
                    v___x_4236_ = lean_box(0);
                    v___x_4237_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4237_, 0, v___x_4236_);
                    return v___x_4237_;
                }
            }
            1 => {
                v___x_4081_ = lean_box(0);
                v___x_4082_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4082_, 0, v___x_4081_);
                return v___x_4082_;
            }
            2 => {
                v___x_4084_ = lean_box(0);
                v___x_4085_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4085_, 0, v___x_4084_);
                return v___x_4085_;
            }
            3 => {
                v___x_4087_ = lean_box(0);
                v___x_4088_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4088_, 0, v___x_4087_);
                return v___x_4088_;
            }
            4 => {
                v___x_4090_ = lean_box(0);
                v___x_4091_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4091_, 0, v___x_4090_);
                return v___x_4091_;
            }
            5 => {
                v___x_4093_ = lean_box(0);
                v___x_4094_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4094_, 0, v___x_4093_);
                return v___x_4094_;
            }
            6 => {
                v___x_4096_ = lean_box(0);
                v___x_4097_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4097_, 0, v___x_4096_);
                return v___x_4097_;
            }
            7 => match v_status_4074_ {
                0 => {
                    if v___y_4102_ == 1 {
                        lean_dec_ref(v_suffix_4075_);
                        lean_dec(v_declName_4073_);
                        state = 6;
                        continue;
                    } else {
                        if v___x_4100_ == 0 {
                            v___x_4105_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__1);
                            v___x_4106_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4107_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4107_, 0, v___x_4105_);
                            lean_ctor_set(v___x_4107_, 1, v___x_4106_);
                            v___x_4108_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
                            v___x_4109_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4109_, 0, v___x_4107_);
                            lean_ctor_set(v___x_4109_, 1, v___x_4108_);
                            v___x_4110_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4111_ = l_Lean_stringToMessageData(v___x_4110_);
                            v___x_4112_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4112_, 0, v___x_4109_);
                            lean_ctor_set(v___x_4112_, 1, v___x_4111_);
                            v___x_4113_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4114_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4114_, 0, v___x_4112_);
                            lean_ctor_set(v___x_4114_, 1, v___x_4113_);
                            v___x_4115_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4115_, 0, v___x_4114_);
                            lean_ctor_set(v___x_4115_, 1, v_suffix_4075_);
                            v___x_4116_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4115_, v___y_4103_, v___y_4104_);
                            return v___x_4116_;
                        } else {
                            lean_dec_ref(v_suffix_4075_);
                            lean_dec(v_declName_4073_);
                            state = 6;
                            continue;
                        }
                    }
                }
                1 => {
                    v___x_4117_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__5);
                    v___x_4118_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                    v___x_4119_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4119_, 0, v___x_4117_);
                    lean_ctor_set(v___x_4119_, 1, v___x_4118_);
                    v___x_4120_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__7);
                    v___x_4121_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4121_, 0, v___x_4119_);
                    lean_ctor_set(v___x_4121_, 1, v___x_4120_);
                    v___x_4122_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4122_, 0, v___x_4121_);
                    lean_ctor_set(v___x_4122_, 1, v_suffix_4075_);
                    v___x_4123_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4122_, v___y_4103_, v___y_4104_);
                    return v___x_4123_;
                }
                2 => match v___y_4102_ {
                    1 => {
                        lean_dec_ref(v_suffix_4075_);
                        lean_dec(v_declName_4073_);
                        state = 5;
                        continue;
                    }
                    3 => {
                        lean_dec_ref(v_suffix_4075_);
                        lean_dec(v_declName_4073_);
                        state = 5;
                        continue;
                    }
                    _ => {
                        if v___x_4100_ == 0 {
                            v___x_4124_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__9);
                            v___x_4125_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4126_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4126_, 0, v___x_4124_);
                            lean_ctor_set(v___x_4126_, 1, v___x_4125_);
                            v___x_4127_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__11);
                            v___x_4128_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4128_, 0, v___x_4126_);
                            lean_ctor_set(v___x_4128_, 1, v___x_4127_);
                            v___x_4129_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
                            v___x_4131_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4131_, 0, v___x_4128_);
                            lean_ctor_set(v___x_4131_, 1, v___x_4130_);
                            v___x_4132_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4133_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4133_, 0, v___x_4131_);
                            lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                            v___x_4134_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4134_, 0, v___x_4133_);
                            lean_ctor_set(v___x_4134_, 1, v_suffix_4075_);
                            v___x_4135_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4134_, v___y_4103_, v___y_4104_);
                            return v___x_4135_;
                        } else {
                            lean_dec_ref(v_suffix_4075_);
                            lean_dec(v_declName_4073_);
                            state = 5;
                            continue;
                        }
                    }
                },
                _ => {
                    if v___y_4102_ == 1 {
                        lean_dec_ref(v_suffix_4075_);
                        lean_dec(v_declName_4073_);
                        state = 4;
                        continue;
                    } else {
                        if v___x_4100_ == 0 {
                            v___x_4136_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__13);
                            v___x_4137_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4138_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4138_, 0, v___x_4136_);
                            lean_ctor_set(v___x_4138_, 1, v___x_4137_);
                            v___x_4139_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__3);
                            v___x_4140_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4140_, 0, v___x_4138_);
                            lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                            v___x_4141_ = l_Lean_ReducibilityStatus_toAttrString(v___y_4102_);
                            v___x_4142_ = l_Lean_stringToMessageData(v___x_4141_);
                            v___x_4143_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4143_, 0, v___x_4140_);
                            lean_ctor_set(v___x_4143_, 1, v___x_4142_);
                            v___x_4144_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg___closed__3);
                            v___x_4145_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4145_, 0, v___x_4143_);
                            lean_ctor_set(v___x_4145_, 1, v___x_4144_);
                            v___x_4146_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                            lean_ctor_set(v___x_4146_, 1, v_suffix_4075_);
                            v___x_4147_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4146_, v___y_4103_, v___y_4104_);
                            return v___x_4147_;
                        } else {
                            lean_dec_ref(v_suffix_4075_);
                            lean_dec(v_declName_4073_);
                            state = 4;
                            continue;
                        }
                    }
                }
            },
            8 => {
                v___x_4152_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__15);
                v___x_4153_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                v___x_4154_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4154_, 0, v___x_4152_);
                lean_ctor_set(v___x_4154_, 1, v___x_4153_);
                v___x_4155_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__17);
                v___x_4156_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4156_, 0, v___x_4154_);
                lean_ctor_set(v___x_4156_, 1, v___x_4155_);
                v___x_4157_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_4157_, 0, v___x_4156_);
                lean_ctor_set(v___x_4157_, 1, v_suffix_4075_);
                v___x_4158_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4157_, v___y_4151_, v___y_4149_);
                return v___x_4158_;
            }
            9 => {
                v___x_4162_ = lean_st_ref_get(v___y_4161_);
                v_env_4163_ = lean_ctor_get(v___x_4162_, 0);
                lean_inc_ref(v_env_4163_);
                lean_dec(v___x_4162_);
                lean_inc(v_declName_4073_);
                v___x_4164_ = lean_get_reducibility_status(v_env_4163_, v_declName_4073_);
                match v_attrKind_4076_ {
                    0 => {
                        v___x_4165_ = lean_st_ref_get(v___y_4161_);
                        v_env_4166_ = lean_ctor_get(v___x_4165_, 0);
                        lean_inc_ref(v_env_4166_);
                        lean_dec(v___x_4165_);
                        v___x_4167_ =
                            l_Lean_Environment_getModuleIdxFor_x3f(v_env_4166_, v_declName_4073_);
                        lean_dec_ref(v_env_4166_);
                        if lean_obj_tag(v___x_4167_) == 1 {
                            lean_dec_ref_known(v___x_4167_, 1);
                            v___y_4149_ = v___y_4161_;
                            v___y_4150_ = v___x_4164_;
                            v___y_4151_ = v___y_4160_;
                            state = 8;
                            continue;
                        } else {
                            lean_dec(v___x_4167_);
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
                            v___x_4168_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__19);
                            v___x_4169_ =
                                l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                            v___x_4170_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4170_, 0, v___x_4168_);
                            lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                            v___x_4171_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__21);
                            v___x_4172_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4172_, 0, v___x_4170_);
                            lean_ctor_set(v___x_4172_, 1, v___x_4171_);
                            v___x_4173_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4173_, 0, v___x_4172_);
                            lean_ctor_set(v___x_4173_, 1, v_suffix_4075_);
                            v___x_4174_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4173_, v___y_4160_, v___y_4161_);
                            return v___x_4174_;
                        }
                        1 => {
                            if v___x_4164_ == 2 {
                                lean_dec_ref(v_suffix_4075_);
                                lean_dec(v_declName_4073_);
                                state = 1;
                                continue;
                            } else {
                                if v___x_4100_ == 0 {
                                    v___x_4175_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__23);
                                    v___x_4176_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4177_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4177_, 0, v___x_4175_);
                                    lean_ctor_set(v___x_4177_, 1, v___x_4176_);
                                    v___x_4178_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4179_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4179_, 0, v___x_4177_);
                                    lean_ctor_set(v___x_4179_, 1, v___x_4178_);
                                    v___x_4180_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4181_ = l_Lean_stringToMessageData(v___x_4180_);
                                    v___x_4182_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4182_, 0, v___x_4179_);
                                    lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                                    v___x_4183_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__27);
                                    v___x_4184_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4184_, 0, v___x_4182_);
                                    lean_ctor_set(v___x_4184_, 1, v___x_4183_);
                                    v___x_4185_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4185_, 0, v___x_4184_);
                                    lean_ctor_set(v___x_4185_, 1, v_suffix_4075_);
                                    v___x_4186_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4185_, v___y_4160_, v___y_4161_);
                                    return v___x_4186_;
                                } else {
                                    lean_dec_ref(v_suffix_4075_);
                                    lean_dec(v_declName_4073_);
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        2 => match v___x_4164_ {
                            1 => {
                                lean_dec_ref(v_suffix_4075_);
                                lean_dec(v_declName_4073_);
                                state = 2;
                                continue;
                            }
                            3 => {
                                lean_dec_ref(v_suffix_4075_);
                                lean_dec(v_declName_4073_);
                                state = 2;
                                continue;
                            }
                            _ => {
                                if v___x_4100_ == 0 {
                                    v___x_4187_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__29);
                                    v___x_4188_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4189_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4189_, 0, v___x_4187_);
                                    lean_ctor_set(v___x_4189_, 1, v___x_4188_);
                                    v___x_4190_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4191_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4191_, 0, v___x_4189_);
                                    lean_ctor_set(v___x_4191_, 1, v___x_4190_);
                                    v___x_4192_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4193_ = l_Lean_stringToMessageData(v___x_4192_);
                                    v___x_4194_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4194_, 0, v___x_4191_);
                                    lean_ctor_set(v___x_4194_, 1, v___x_4193_);
                                    v___x_4195_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__31);
                                    v___x_4196_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4196_, 0, v___x_4194_);
                                    lean_ctor_set(v___x_4196_, 1, v___x_4195_);
                                    v___x_4197_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                                    lean_ctor_set(v___x_4197_, 1, v_suffix_4075_);
                                    v___x_4198_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4197_, v___y_4160_, v___y_4161_);
                                    return v___x_4198_;
                                } else {
                                    lean_dec_ref(v_suffix_4075_);
                                    lean_dec(v_declName_4073_);
                                    state = 2;
                                    continue;
                                }
                            }
                        },
                        _ => {
                            if v___x_4164_ == 1 {
                                lean_dec_ref(v_suffix_4075_);
                                lean_dec(v_declName_4073_);
                                state = 3;
                                continue;
                            } else {
                                if v___x_4100_ == 0 {
                                    v___x_4199_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__33);
                                    v___x_4200_ = l_Lean_MessageData_ofConstName(
                                        v_declName_4073_,
                                        v___x_4100_,
                                    );
                                    v___x_4201_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4201_, 0, v___x_4199_);
                                    lean_ctor_set(v___x_4201_, 1, v___x_4200_);
                                    v___x_4202_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__25);
                                    v___x_4203_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4203_, 0, v___x_4201_);
                                    lean_ctor_set(v___x_4203_, 1, v___x_4202_);
                                    v___x_4204_ =
                                        l_Lean_ReducibilityStatus_toAttrString(v___x_4164_);
                                    v___x_4205_ = l_Lean_stringToMessageData(v___x_4204_);
                                    v___x_4206_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4206_, 0, v___x_4203_);
                                    lean_ctor_set(v___x_4206_, 1, v___x_4205_);
                                    v___x_4207_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__35);
                                    v___x_4208_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4208_, 0, v___x_4206_);
                                    lean_ctor_set(v___x_4208_, 1, v___x_4207_);
                                    v___x_4209_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_4209_, 0, v___x_4208_);
                                    lean_ctor_set(v___x_4209_, 1, v_suffix_4075_);
                                    v___x_4210_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4209_, v___y_4160_, v___y_4161_);
                                    return v___x_4210_;
                                } else {
                                    lean_dec_ref(v_suffix_4075_);
                                    lean_dec(v_declName_4073_);
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    },
                    _ => {
                        v___x_4211_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__37);
                        v___x_4212_ = l_Lean_MessageData_ofConstName(v_declName_4073_, v___x_4100_);
                        v___x_4213_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4213_, 0, v___x_4211_);
                        lean_ctor_set(v___x_4213_, 1, v___x_4212_);
                        v___x_4214_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39_once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___closed__39);
                        v___x_4215_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4215_, 0, v___x_4213_);
                        lean_ctor_set(v___x_4215_, 1, v___x_4214_);
                        v___x_4216_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_4216_, 0, v___x_4215_);
                        lean_ctor_set(v___x_4216_, 1, v_suffix_4075_);
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
                    v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
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
    mut v_declName_4238_: *mut LeanObject,
    mut v_status_4239_: *mut LeanObject,
    mut v_suffix_4240_: *mut LeanObject,
    mut v_attrKind_4241_: *mut LeanObject,
    mut v___y_4242_: *mut LeanObject,
    mut v___y_4243_: *mut LeanObject,
    mut v___y_4244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_status_boxed_4245_: u8 = 0;
    let mut v_attrKind_boxed_4246_: u8 = 0;
    let mut v_res_4247_: *mut LeanObject = core::ptr::null_mut();
    v_status_boxed_4245_ = (lean_unbox(v_status_4239_) as u8);
    v_attrKind_boxed_4246_ = (lean_unbox(v_attrKind_4241_) as u8);
    v_res_4247_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0(
        v_declName_4238_,
        v_status_boxed_4245_,
        v_suffix_4240_,
        v_attrKind_boxed_4246_,
        v___y_4242_,
        v___y_4243_,
    );
    lean_dec(v___y_4243_);
    lean_dec_ref(v___y_4242_);
    return v_res_4247_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(
    mut v___y_4248_: *mut LeanObject,
    mut v_isExporting_4249_: u8,
    mut v___x_4250_: *mut LeanObject,
    mut v_a_x3f_4251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4264_: u8 = 0;
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_unused_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4253_ = lean_st_ref_take(v___y_4248_);
                v_env_4254_ = lean_ctor_get(v___x_4253_, 0);
                v_nextMacroScope_4255_ = lean_ctor_get(v___x_4253_, 1);
                v_ngen_4256_ = lean_ctor_get(v___x_4253_, 2);
                v_auxDeclNGen_4257_ = lean_ctor_get(v___x_4253_, 3);
                v_traceState_4258_ = lean_ctor_get(v___x_4253_, 4);
                v_messages_4259_ = lean_ctor_get(v___x_4253_, 6);
                v_infoState_4260_ = lean_ctor_get(v___x_4253_, 7);
                v_snapshotTasks_4261_ = lean_ctor_get(v___x_4253_, 8);
                v_isSharedCheck_4272_ = (!lean_is_exclusive(v___x_4253_)) as u8;
                if v_isSharedCheck_4272_ == 0 {
                    v_unused_4273_ = lean_ctor_get(v___x_4253_, 5);
                    lean_dec(v_unused_4273_);
                    v___x_4263_ = v___x_4253_;
                    v_isShared_4264_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4261_);
                    lean_inc(v_infoState_4260_);
                    lean_inc(v_messages_4259_);
                    lean_inc(v_traceState_4258_);
                    lean_inc(v_auxDeclNGen_4257_);
                    lean_inc(v_ngen_4256_);
                    lean_inc(v_nextMacroScope_4255_);
                    lean_inc(v_env_4254_);
                    lean_dec(v___x_4253_);
                    v___x_4263_ = lean_box(0);
                    v_isShared_4264_ = v_isSharedCheck_4272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4265_ = l_Lean_Environment_setExporting(v_env_4254_, v_isExporting_4249_);
                if v_isShared_4264_ == 0 {
                    lean_ctor_set(v___x_4263_, 5, v___x_4250_);
                    lean_ctor_set(v___x_4263_, 0, v___x_4265_);
                    v___x_4267_ = v___x_4263_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4265_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 1, v_nextMacroScope_4255_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 2, v_ngen_4256_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 3, v_auxDeclNGen_4257_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 4, v_traceState_4258_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 5, v___x_4250_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 6, v_messages_4259_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 7, v_infoState_4260_);
                    lean_ctor_set(v_reuseFailAlloc_4271_, 8, v_snapshotTasks_4261_);
                    v___x_4267_ = v_reuseFailAlloc_4271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4268_ = lean_st_ref_set(v___y_4248_, v___x_4267_);
                v___x_4269_ = lean_box(0);
                v___x_4270_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4270_, 0, v___x_4269_);
                return v___x_4270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0___boxed(
    mut v___y_4274_: *mut LeanObject,
    mut v_isExporting_4275_: *mut LeanObject,
    mut v___x_4276_: *mut LeanObject,
    mut v_a_x3f_4277_: *mut LeanObject,
    mut v___y_4278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4279_: u8 = 0;
    let mut v_res_4280_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4279_ = (lean_unbox(v_isExporting_4275_) as u8);
    v_res_4280_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4274_, v_isExporting_boxed_4279_, v___x_4276_, v_a_x3f_4277_);
    lean_dec(v_a_x3f_4277_);
    lean_dec(v___y_4274_);
    return v_res_4280_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    v___x_4281_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4281_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    v___x_4282_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__0);
    v___x_4283_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4283_, 0, v___x_4282_);
    return v___x_4283_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    v___x_4284_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__1);
    v___x_4285_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4285_, 0, v___x_4284_);
    lean_ctor_set(v___x_4285_, 1, v___x_4284_);
    return v___x_4285_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(
    mut v_x_4286_: *mut LeanObject,
    mut v_isExporting_4287_: u8,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4293_: u8 = 0;
    let mut v___x_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4305_: u8 = 0;
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4325_: u8 = 0;
    let mut v_unused_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_unused_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_unused_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4291_ = lean_st_ref_get(v___y_4289_);
                v_env_4292_ = lean_ctor_get(v___x_4291_, 0);
                lean_inc_ref(v_env_4292_);
                lean_dec(v___x_4291_);
                v_isExporting_4293_ = lean_ctor_get_uint8(
                    v_env_4292_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4292_);
                v___x_4294_ = lean_st_ref_take(v___y_4289_);
                v_env_4295_ = lean_ctor_get(v___x_4294_, 0);
                v_nextMacroScope_4296_ = lean_ctor_get(v___x_4294_, 1);
                v_ngen_4297_ = lean_ctor_get(v___x_4294_, 2);
                v_auxDeclNGen_4298_ = lean_ctor_get(v___x_4294_, 3);
                v_traceState_4299_ = lean_ctor_get(v___x_4294_, 4);
                v_messages_4300_ = lean_ctor_get(v___x_4294_, 6);
                v_infoState_4301_ = lean_ctor_get(v___x_4294_, 7);
                v_snapshotTasks_4302_ = lean_ctor_get(v___x_4294_, 8);
                v_isSharedCheck_4341_ = (!lean_is_exclusive(v___x_4294_)) as u8;
                if v_isSharedCheck_4341_ == 0 {
                    v_unused_4342_ = lean_ctor_get(v___x_4294_, 5);
                    lean_dec(v_unused_4342_);
                    v___x_4304_ = v___x_4294_;
                    v_isShared_4305_ = v_isSharedCheck_4341_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4302_);
                    lean_inc(v_infoState_4301_);
                    lean_inc(v_messages_4300_);
                    lean_inc(v_traceState_4299_);
                    lean_inc(v_auxDeclNGen_4298_);
                    lean_inc(v_ngen_4297_);
                    lean_inc(v_nextMacroScope_4296_);
                    lean_inc(v_env_4295_);
                    lean_dec(v___x_4294_);
                    v___x_4304_ = lean_box(0);
                    v_isShared_4305_ = v_isSharedCheck_4341_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4306_ = l_Lean_Environment_setExporting(v_env_4295_, v_isExporting_4287_);
                v___x_4307_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
                if v_isShared_4305_ == 0 {
                    lean_ctor_set(v___x_4304_, 5, v___x_4307_);
                    lean_ctor_set(v___x_4304_, 0, v___x_4306_);
                    v___x_4309_ = v___x_4304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 0, v___x_4306_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_nextMacroScope_4296_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_ngen_4297_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_auxDeclNGen_4298_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 4, v_traceState_4299_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 5, v___x_4307_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 6, v_messages_4300_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 7, v_infoState_4301_);
                    lean_ctor_set(v_reuseFailAlloc_4340_, 8, v_snapshotTasks_4302_);
                    v___x_4309_ = v_reuseFailAlloc_4340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4310_ = lean_st_ref_set(v___y_4289_, v___x_4309_);
                lean_inc(v___y_4289_);
                lean_inc_ref(v___y_4288_);
                v_r_4311_ = lean_apply_3(v_x_4286_, v___y_4288_, v___y_4289_, lean_box(0));
                if lean_obj_tag(v_r_4311_) == 0 {
                    v_a_4312_ = lean_ctor_get(v_r_4311_, 0);
                    v_isSharedCheck_4328_ = (!lean_is_exclusive(v_r_4311_)) as u8;
                    if v_isSharedCheck_4328_ == 0 {
                        v___x_4314_ = v_r_4311_;
                        v_isShared_4315_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4312_);
                        lean_dec(v_r_4311_);
                        v___x_4314_ = lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_4329_ = lean_ctor_get(v_r_4311_, 0);
                    lean_inc(v_a_4329_);
                    lean_dec_ref_known(v_r_4311_, 1);
                    v___x_4330_ = lean_box(0);
                    v___x_4331_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4289_, v_isExporting_4293_, v___x_4307_, v___x_4330_);
                    v_isSharedCheck_4338_ = (!lean_is_exclusive(v___x_4331_)) as u8;
                    if v_isSharedCheck_4338_ == 0 {
                        v_unused_4339_ = lean_ctor_get(v___x_4331_, 0);
                        lean_dec(v_unused_4339_);
                        v___x_4333_ = v___x_4331_;
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_4331_);
                        v___x_4333_ = lean_box(0);
                        v_isShared_4334_ = v_isSharedCheck_4338_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_4312_);
                if v_isShared_4315_ == 0 {
                    lean_ctor_set_tag(v___x_4314_, 1);
                    v___x_4317_ = v___x_4314_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4312_);
                    v___x_4317_ = v_reuseFailAlloc_4327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4318_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___lam__0(v___y_4289_, v_isExporting_4293_, v___x_4307_, v___x_4317_);
                lean_dec_ref(v___x_4317_);
                v_isSharedCheck_4325_ = (!lean_is_exclusive(v___x_4318_)) as u8;
                if v_isSharedCheck_4325_ == 0 {
                    v_unused_4326_ = lean_ctor_get(v___x_4318_, 0);
                    lean_dec(v_unused_4326_);
                    v___x_4320_ = v___x_4318_;
                    v_isShared_4321_ = v_isSharedCheck_4325_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_4318_);
                    v___x_4320_ = lean_box(0);
                    v_isShared_4321_ = v_isSharedCheck_4325_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_4321_ == 0 {
                    lean_ctor_set(v___x_4320_, 0, v_a_4312_);
                    v___x_4323_ = v___x_4320_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4312_);
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
                    lean_ctor_set_tag(v___x_4333_, 1);
                    lean_ctor_set(v___x_4333_, 0, v_a_4329_);
                    v___x_4336_ = v___x_4333_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4329_);
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
    mut v_x_4343_: *mut LeanObject,
    mut v_isExporting_4344_: *mut LeanObject,
    mut v___y_4345_: *mut LeanObject,
    mut v___y_4346_: *mut LeanObject,
    mut v___y_4347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4348_: u8 = 0;
    let mut v_res_4349_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4348_ = (lean_unbox(v_isExporting_4344_) as u8);
    v_res_4349_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4343_, v_isExporting_boxed_4348_, v___y_4345_, v___y_4346_);
    lean_dec(v___y_4346_);
    lean_dec_ref(v___y_4345_);
    return v_res_4349_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(
    mut v_x_4350_: *mut LeanObject,
    mut v_when_4351_: u8,
    mut v___y_4352_: *mut LeanObject,
    mut v___y_4353_: *mut LeanObject,
) -> *mut LeanObject {
    if v_when_4351_ == 0 {
        let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v___y_4353_);
        lean_inc_ref(v___y_4352_);
        v___x_4355_ = lean_apply_3(v_x_4350_, v___y_4352_, v___y_4353_, lean_box(0));
        return v___x_4355_;
    } else {
        let mut v___x_4356_: u8 = 0;
        let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
        v___x_4356_ = 0;
        v___x_4357_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4350_, v___x_4356_, v___y_4352_, v___y_4353_);
        return v___x_4357_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg___boxed(
    mut v_x_4358_: *mut LeanObject,
    mut v_when_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_4363_: u8 = 0;
    let mut v_res_4364_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_4363_ = (lean_unbox(v_when_4359_) as u8);
    v_res_4364_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_4358_, v_when_boxed_4363_, v___y_4360_, v___y_4361_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    return v_res_4364_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__2()
-> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__1;
    v___x_4369_ = l_Lean_MessageData_ofFormat(v___x_4368_);
    return v___x_4369_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3()
-> *mut LeanObject {
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suffix_4371_: *mut LeanObject = core::ptr::null_mut();
    v___x_4370_ = lean_obj_once(
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
    mut v_declName_4372_: *mut LeanObject,
    mut v_status_4373_: u8,
    mut v_attrKind_4374_: u8,
    mut v_a_4375_: *mut LeanObject,
    mut v_a_4376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_suffix_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    v_suffix_4378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3),
        core::ptr::addr_of_mut!(
            l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3_once
        ),
        _init_l___private_Lean_ReducibilityAttrs_0__Lean_validate___closed__3,
    );
    v___x_4379_ = lean_box((v_status_4373_) as usize);
    v___x_4380_ = lean_box((v_attrKind_4374_) as usize);
    v___f_4381_ = lean_alloc_closure(
        l___private_Lean_ReducibilityAttrs_0__Lean_validate___lam__0___boxed
            as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_4381_, 0, v_declName_4372_);
    lean_closure_set(v___f_4381_, 1, v___x_4379_);
    lean_closure_set(v___f_4381_, 2, v_suffix_4378_);
    lean_closure_set(v___f_4381_, 3, v___x_4380_);
    v___x_4382_ = 1;
    v___x_4383_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v___f_4381_, v___x_4382_, v_a_4375_, v_a_4376_);
    return v___x_4383_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_validate___boxed(
    mut v_declName_4384_: *mut LeanObject,
    mut v_status_4385_: *mut LeanObject,
    mut v_attrKind_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_status_boxed_4390_: u8 = 0;
    let mut v_attrKind_boxed_4391_: u8 = 0;
    let mut v_res_4392_: *mut LeanObject = core::ptr::null_mut();
    v_status_boxed_4390_ = (lean_unbox(v_status_4385_) as u8);
    v_attrKind_boxed_4391_ = (lean_unbox(v_attrKind_4386_) as u8);
    v_res_4392_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(
        v_declName_4384_,
        v_status_boxed_4390_,
        v_attrKind_boxed_4391_,
        v_a_4387_,
        v_a_4388_,
    );
    lean_dec(v_a_4388_);
    lean_dec_ref(v_a_4387_);
    return v_res_4392_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(
    mut v_00_u03b1_4393_: *mut LeanObject,
    mut v_msg_4394_: *mut LeanObject,
    mut v___y_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4398_: *mut LeanObject = core::ptr::null_mut();
    v___x_4398_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v_msg_4394_, v___y_4395_, v___y_4396_);
    return v___x_4398_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___boxed(
    mut v_00_u03b1_4399_: *mut LeanObject,
    mut v_msg_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4404_: *mut LeanObject = core::ptr::null_mut();
    v_res_4404_ =
        l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1(
            v_00_u03b1_4399_,
            v_msg_4400_,
            v___y_4401_,
            v___y_4402_,
        );
    lean_dec(v___y_4402_);
    lean_dec_ref(v___y_4401_);
    return v_res_4404_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(
    mut v_00_u03b1_4405_: *mut LeanObject,
    mut v_x_4406_: *mut LeanObject,
    mut v_isExporting_4407_: u8,
    mut v___y_4408_: *mut LeanObject,
    mut v___y_4409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    v___x_4411_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg(v_x_4406_, v_isExporting_4407_, v___y_4408_, v___y_4409_);
    return v___x_4411_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___boxed(
    mut v_00_u03b1_4412_: *mut LeanObject,
    mut v_x_4413_: *mut LeanObject,
    mut v_isExporting_4414_: *mut LeanObject,
    mut v___y_4415_: *mut LeanObject,
    mut v___y_4416_: *mut LeanObject,
    mut v___y_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_4418_: u8 = 0;
    let mut v_res_4419_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4418_ = (lean_unbox(v_isExporting_4414_) as u8);
    v_res_4419_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5(v_00_u03b1_4412_, v_x_4413_, v_isExporting_boxed_4418_, v___y_4415_, v___y_4416_);
    lean_dec(v___y_4416_);
    lean_dec_ref(v___y_4415_);
    return v_res_4419_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(
    mut v_00_u03b1_4420_: *mut LeanObject,
    mut v_x_4421_: *mut LeanObject,
    mut v_when_4422_: u8,
    mut v___y_4423_: *mut LeanObject,
    mut v___y_4424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4426_: *mut LeanObject = core::ptr::null_mut();
    v___x_4426_ = l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___redArg(v_x_4421_, v_when_4422_, v___y_4423_, v___y_4424_);
    return v___x_4426_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3___boxed(
    mut v_00_u03b1_4427_: *mut LeanObject,
    mut v_x_4428_: *mut LeanObject,
    mut v_when_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
    mut v___y_4431_: *mut LeanObject,
    mut v___y_4432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_when_boxed_4433_: u8 = 0;
    let mut v_res_4434_: *mut LeanObject = core::ptr::null_mut();
    v_when_boxed_4433_ = (lean_unbox(v_when_4429_) as u8);
    v_res_4434_ =
        l_Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3(
            v_00_u03b1_4427_,
            v_x_4428_,
            v_when_boxed_4433_,
            v___y_4430_,
            v___y_4431_,
        );
    lean_dec(v___y_4431_);
    lean_dec_ref(v___y_4430_);
    return v_res_4434_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(
    mut v_00_u03b1_4435_: *mut LeanObject,
    mut v_constName_4436_: *mut LeanObject,
    mut v___y_4437_: *mut LeanObject,
    mut v___y_4438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    v___x_4440_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___redArg(v_constName_4436_, v___y_4437_, v___y_4438_);
    return v___x_4440_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3___boxed(
    mut v_00_u03b1_4441_: *mut LeanObject,
    mut v_constName_4442_: *mut LeanObject,
    mut v___y_4443_: *mut LeanObject,
    mut v___y_4444_: *mut LeanObject,
    mut v___y_4445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4446_: *mut LeanObject = core::ptr::null_mut();
    v_res_4446_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3(v_00_u03b1_4441_, v_constName_4442_, v___y_4443_, v___y_4444_);
    lean_dec(v___y_4444_);
    lean_dec_ref(v___y_4443_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(
    mut v_00_u03b1_4447_: *mut LeanObject,
    mut v_ref_4448_: *mut LeanObject,
    mut v_constName_4449_: *mut LeanObject,
    mut v___y_4450_: *mut LeanObject,
    mut v___y_4451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    v___x_4453_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___redArg(v_ref_4448_, v_constName_4449_, v___y_4450_, v___y_4451_);
    return v___x_4453_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b1_4454_: *mut LeanObject,
    mut v_ref_4455_: *mut LeanObject,
    mut v_constName_4456_: *mut LeanObject,
    mut v___y_4457_: *mut LeanObject,
    mut v___y_4458_: *mut LeanObject,
    mut v___y_4459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4460_: *mut LeanObject = core::ptr::null_mut();
    v_res_4460_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4(v_00_u03b1_4454_, v_ref_4455_, v_constName_4456_, v___y_4457_, v___y_4458_);
    lean_dec(v___y_4458_);
    lean_dec_ref(v___y_4457_);
    lean_dec(v_ref_4455_);
    return v_res_4460_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(
    mut v_00_u03b1_4461_: *mut LeanObject,
    mut v_ref_4462_: *mut LeanObject,
    mut v_msg_4463_: *mut LeanObject,
    mut v_declHint_4464_: *mut LeanObject,
    mut v___y_4465_: *mut LeanObject,
    mut v___y_4466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___redArg(v_ref_4462_, v_msg_4463_, v_declHint_4464_, v___y_4465_, v___y_4466_);
    return v___x_4468_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7___boxed(
    mut v_00_u03b1_4469_: *mut LeanObject,
    mut v_ref_4470_: *mut LeanObject,
    mut v_msg_4471_: *mut LeanObject,
    mut v_declHint_4472_: *mut LeanObject,
    mut v___y_4473_: *mut LeanObject,
    mut v___y_4474_: *mut LeanObject,
    mut v___y_4475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4476_: *mut LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7(v_00_u03b1_4469_, v_ref_4470_, v_msg_4471_, v_declHint_4472_, v___y_4473_, v___y_4474_);
    lean_dec(v___y_4474_);
    lean_dec_ref(v___y_4473_);
    lean_dec(v_ref_4470_);
    return v_res_4476_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(
    mut v_msg_4477_: *mut LeanObject,
    mut v_declHint_4478_: *mut LeanObject,
    mut v___y_4479_: *mut LeanObject,
    mut v___y_4480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    v___x_4482_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___redArg(v_msg_4477_, v_declHint_4478_, v___y_4480_);
    return v___x_4482_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9___boxed(
    mut v_msg_4483_: *mut LeanObject,
    mut v_declHint_4484_: *mut LeanObject,
    mut v___y_4485_: *mut LeanObject,
    mut v___y_4486_: *mut LeanObject,
    mut v___y_4487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4488_: *mut LeanObject = core::ptr::null_mut();
    v_res_4488_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__8_spec__9(v_msg_4483_, v_declHint_4484_, v___y_4485_, v___y_4486_);
    lean_dec(v___y_4486_);
    lean_dec_ref(v___y_4485_);
    return v_res_4488_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(
    mut v_00_u03b1_4489_: *mut LeanObject,
    mut v_ref_4490_: *mut LeanObject,
    mut v_msg_4491_: *mut LeanObject,
    mut v___y_4492_: *mut LeanObject,
    mut v___y_4493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___redArg(v_ref_4490_, v_msg_4491_, v___y_4492_, v___y_4493_);
    return v___x_4495_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9___boxed(
    mut v_00_u03b1_4496_: *mut LeanObject,
    mut v_ref_4497_: *mut LeanObject,
    mut v_msg_4498_: *mut LeanObject,
    mut v___y_4499_: *mut LeanObject,
    mut v___y_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_res_4502_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__2_spec__3_spec__4_spec__7_spec__9(v_00_u03b1_4496_, v_ref_4497_, v_msg_4498_, v___y_4499_, v___y_4500_);
    lean_dec(v___y_4500_);
    lean_dec_ref(v___y_4499_);
    lean_dec(v_ref_4497_);
    return v_res_4502_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(
    mut v_status_4503_: u8,
    mut v_declName_4504_: *mut LeanObject,
    mut v_stx_4505_: *mut LeanObject,
    mut v_attrKind_4506_: u8,
    mut v_a_4507_: *mut LeanObject,
    mut v_a_4508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4514_: u8 = 0;
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_unused_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4540_: u8 = 0;
    let mut v_unused_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4510_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_4505_, v_a_4507_, v_a_4508_);
                if lean_obj_tag(v___x_4510_) == 0 {
                    lean_dec_ref_known(v___x_4510_, 1);
                    lean_inc(v_declName_4504_);
                    v___x_4511_ = l___private_Lean_ReducibilityAttrs_0__Lean_validate(
                        v_declName_4504_,
                        v_status_4503_,
                        v_attrKind_4506_,
                        v_a_4507_,
                        v_a_4508_,
                    );
                    if lean_obj_tag(v___x_4511_) == 0 {
                        v_isSharedCheck_4540_ = (!lean_is_exclusive(v___x_4511_)) as u8;
                        if v_isSharedCheck_4540_ == 0 {
                            v_unused_4541_ = lean_ctor_get(v___x_4511_, 0);
                            lean_dec(v_unused_4541_);
                            v___x_4513_ = v___x_4511_;
                            v_isShared_4514_ = v_isSharedCheck_4540_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_4511_);
                            v___x_4513_ = lean_box(0);
                            v_isShared_4514_ = v_isSharedCheck_4540_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_4504_);
                        return v___x_4511_;
                    }
                } else {
                    lean_dec(v_declName_4504_);
                    return v___x_4510_;
                }
            }
            1 => {
                v___x_4515_ = lean_st_ref_take(v_a_4508_);
                v_currNamespace_4516_ = lean_ctor_get(v_a_4507_, 6);
                v_env_4517_ = lean_ctor_get(v___x_4515_, 0);
                v_nextMacroScope_4518_ = lean_ctor_get(v___x_4515_, 1);
                v_ngen_4519_ = lean_ctor_get(v___x_4515_, 2);
                v_auxDeclNGen_4520_ = lean_ctor_get(v___x_4515_, 3);
                v_traceState_4521_ = lean_ctor_get(v___x_4515_, 4);
                v_messages_4522_ = lean_ctor_get(v___x_4515_, 6);
                v_infoState_4523_ = lean_ctor_get(v___x_4515_, 7);
                v_snapshotTasks_4524_ = lean_ctor_get(v___x_4515_, 8);
                v_isSharedCheck_4538_ = (!lean_is_exclusive(v___x_4515_)) as u8;
                if v_isSharedCheck_4538_ == 0 {
                    v_unused_4539_ = lean_ctor_get(v___x_4515_, 5);
                    lean_dec(v_unused_4539_);
                    v___x_4526_ = v___x_4515_;
                    v_isShared_4527_ = v_isSharedCheck_4538_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4524_);
                    lean_inc(v_infoState_4523_);
                    lean_inc(v_messages_4522_);
                    lean_inc(v_traceState_4521_);
                    lean_inc(v_auxDeclNGen_4520_);
                    lean_inc(v_ngen_4519_);
                    lean_inc(v_nextMacroScope_4518_);
                    lean_inc(v_env_4517_);
                    lean_dec(v___x_4515_);
                    v___x_4526_ = lean_box(0);
                    v_isShared_4527_ = v_isSharedCheck_4538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_currNamespace_4516_);
                v___x_4528_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_4517_,
                    v_declName_4504_,
                    v_status_4503_,
                    v_attrKind_4506_,
                    v_currNamespace_4516_,
                );
                v___x_4529_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__3_spec__5___redArg___closed__2);
                if v_isShared_4527_ == 0 {
                    lean_ctor_set(v___x_4526_, 5, v___x_4529_);
                    lean_ctor_set(v___x_4526_, 0, v___x_4528_);
                    v___x_4531_ = v___x_4526_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4528_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_nextMacroScope_4518_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 2, v_ngen_4519_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 3, v_auxDeclNGen_4520_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 4, v_traceState_4521_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 5, v___x_4529_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 6, v_messages_4522_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 7, v_infoState_4523_);
                    lean_ctor_set(v_reuseFailAlloc_4537_, 8, v_snapshotTasks_4524_);
                    v___x_4531_ = v_reuseFailAlloc_4537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4532_ = lean_st_ref_set(v_a_4508_, v___x_4531_);
                v___x_4533_ = lean_box(0);
                if v_isShared_4514_ == 0 {
                    lean_ctor_set(v___x_4513_, 0, v___x_4533_);
                    v___x_4535_ = v___x_4513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
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
    mut v_status_4542_: *mut LeanObject,
    mut v_declName_4543_: *mut LeanObject,
    mut v_stx_4544_: *mut LeanObject,
    mut v_attrKind_4545_: *mut LeanObject,
    mut v_a_4546_: *mut LeanObject,
    mut v_a_4547_: *mut LeanObject,
    mut v_a_4548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_status_boxed_4549_: u8 = 0;
    let mut v_attrKind_boxed_4550_: u8 = 0;
    let mut v_res_4551_: *mut LeanObject = core::ptr::null_mut();
    v_status_boxed_4549_ = (lean_unbox(v_status_4542_) as u8);
    v_attrKind_boxed_4550_ = (lean_unbox(v_attrKind_4545_) as u8);
    v_res_4551_ = l___private_Lean_ReducibilityAttrs_0__Lean_addAttr(
        v_status_boxed_4549_,
        v_declName_4543_,
        v_stx_4544_,
        v_attrKind_boxed_4550_,
        v_a_4546_,
        v_a_4547_,
    );
    lean_dec(v_a_4547_);
    lean_dec_ref(v_a_4546_);
    return v_res_4551_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    v___x_4553_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4554_ = l_Lean_stringToMessageData(v___x_4553_);
    return v___x_4554_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4556_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4557_ = l_Lean_stringToMessageData(v___x_4556_);
    return v___x_4557_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(
    mut v___x_4558_: *mut LeanObject,
    mut v_decl_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    v___x_4563_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
    v___x_4564_ = l_Lean_MessageData_ofName(v___x_4558_);
    v___x_4565_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4565_, 0, v___x_4563_);
    lean_ctor_set(v___x_4565_, 1, v___x_4564_);
    v___x_4566_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0___closed__3_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_);
    v___x_4567_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4567_, 0, v___x_4565_);
    lean_ctor_set(v___x_4567_, 1, v___x_4566_);
    v___x_4568_ = l_Lean_throwError___at___00__private_Lean_ReducibilityAttrs_0__Lean_validate_spec__1___redArg(v___x_4567_, v___y_4560_, v___y_4561_);
    return v___x_4568_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(
    mut v___x_4569_: *mut LeanObject,
    mut v_decl_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
    mut v___y_4572_: *mut LeanObject,
    mut v___y_4573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4574_: *mut LeanObject = core::ptr::null_mut();
    v_res_4574_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___lam__0_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_(v___x_4569_, v_decl_4570_, v___y_4571_, v___y_4572_);
    lean_dec(v___y_4572_);
    lean_dec_ref(v___y_4571_);
    lean_dec(v_decl_4570_);
    return v_res_4574_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    v___x_4639_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__25_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4640_ = l_Lean_registerBuiltinAttribute(v___x_4639_);
    return v___x_4640_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2____boxed(
    mut v_a_4641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4642_: *mut LeanObject = core::ptr::null_mut();
    v_res_4642_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
    return v_res_4642_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    v___x_4643_ = lean_unsigned_to_nat(4118757939);
    v___x_4644_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4645_ = l_Lean_Name_num___override(v___x_4644_, v___x_4643_);
    return v___x_4645_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    v___x_4646_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4647_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4648_ = l_Lean_Name_str___override(v___x_4647_, v___x_4646_);
    return v___x_4648_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    v___x_4649_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4650_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4651_ = l_Lean_Name_str___override(v___x_4650_, v___x_4649_);
    return v___x_4651_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    v___x_4652_ = lean_unsigned_to_nat(2);
    v___x_4653_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4654_ = l_Lean_Name_num___override(v___x_4653_, v___x_4652_);
    return v___x_4654_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    v___x_4661_ = 0;
    v___x_4662_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4663_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4664_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4665_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_4665_, 0, v___x_4664_);
    lean_ctor_set(v___x_4665_, 1, v___x_4663_);
    lean_ctor_set(v___x_4665_, 2, v___x_4662_);
    lean_ctor_set_uint8(
        v___x_4665_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4661_,
    );
    return v___x_4665_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut LeanObject = core::ptr::null_mut();
    v___f_4669_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4670_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_;
    v___x_4671_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4672_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4672_, 0, v___x_4671_);
    lean_ctor_set(v___x_4672_, 1, v___x_4670_);
    lean_ctor_set(v___x_4672_, 2, v___f_4669_);
    return v___x_4672_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    v___x_4674_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_);
    v___x_4675_ = l_Lean_registerBuiltinAttribute(v___x_4674_);
    return v___x_4675_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2____boxed(
    mut v_a_4676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4677_: *mut LeanObject = core::ptr::null_mut();
    v_res_4677_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
    return v_res_4677_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut LeanObject = core::ptr::null_mut();
    v___x_4678_ = lean_unsigned_to_nat(2994861043);
    v___x_4679_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__12_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4680_ = l_Lean_Name_num___override(v___x_4679_, v___x_4678_);
    return v___x_4680_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    v___x_4681_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__14_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4682_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__0_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4683_ = l_Lean_Name_str___override(v___x_4682_, v___x_4681_);
    return v___x_4683_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut LeanObject = core::ptr::null_mut();
    v___x_4684_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__16_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_;
    v___x_4685_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__1_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4686_ = l_Lean_Name_str___override(v___x_4685_, v___x_4684_);
    return v___x_4686_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut LeanObject = core::ptr::null_mut();
    v___x_4687_ = lean_unsigned_to_nat(2);
    v___x_4688_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__2_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4689_ = l_Lean_Name_num___override(v___x_4688_, v___x_4687_);
    return v___x_4689_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4696_: u8 = 0;
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v___x_4696_ = 0;
    v___x_4697_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__7_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4698_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__5_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4699_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__3_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4700_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_4700_, 0, v___x_4699_);
    lean_ctor_set(v___x_4700_, 1, v___x_4698_);
    lean_ctor_set(v___x_4700_, 2, v___x_4697_);
    lean_ctor_set_uint8(
        v___x_4700_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_4696_,
    );
    return v___x_4700_;
}
pub unsafe fn _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut LeanObject = core::ptr::null_mut();
    v___f_4704_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__6_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4705_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_;
    v___x_4706_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__8_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4707_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_4707_, 0, v___x_4706_);
    lean_ctor_set(v___x_4707_, 1, v___x_4705_);
    lean_ctor_set(v___x_4707_, 2, v___f_4704_);
    return v___x_4707_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    v___x_4709_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2__once), _init_l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_);
    v___x_4710_ = l_Lean_registerBuiltinAttribute(v___x_4709_);
    return v___x_4710_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2____boxed(
    mut v_a_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4712_: *mut LeanObject = core::ptr::null_mut();
    v_res_4712_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
    return v_res_4712_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    v___x_4744_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__10_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_;
    v___x_4745_ = l_Lean_registerBuiltinAttribute(v___x_4744_);
    return v___x_4745_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2____boxed(
    mut v_a_4746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4747_: *mut LeanObject = core::ptr::null_mut();
    v_res_4747_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
    return v_res_4747_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut LeanObject = core::ptr::null_mut();
    v___x_4776_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn___closed__9_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_;
    v___x_4777_ = l_Lean_registerBuiltinAttribute(v___x_4776_);
    return v___x_4777_;
}
pub unsafe fn l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2____boxed(
    mut v_a_4778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4779_: *mut LeanObject = core::ptr::null_mut();
    v_res_4779_ = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
    return v_res_4779_;
}
pub unsafe fn l_Lean_getReducibilityStatus___redArg___lam__0(
    mut v_declName_4780_: *mut LeanObject,
    mut v_toPure_4781_: *mut LeanObject,
    mut v_____do__lift_4782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4783_: u8 = 0;
    let mut v___x_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    v___x_4783_ = lean_get_reducibility_status(v_____do__lift_4782_, v_declName_4780_);
    v___x_4784_ = lean_box((v___x_4783_) as usize);
    v___x_4785_ = lean_apply_2(v_toPure_4781_, lean_box(0), v___x_4784_);
    return v___x_4785_;
}
pub unsafe fn l_Lean_getReducibilityStatus___redArg(
    mut v_inst_4786_: *mut LeanObject,
    mut v_inst_4787_: *mut LeanObject,
    mut v_declName_4788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4789_ = lean_ctor_get(v_inst_4786_, 0);
    lean_inc_ref(v_toApplicative_4789_);
    v_toBind_4790_ = lean_ctor_get(v_inst_4786_, 1);
    lean_inc(v_toBind_4790_);
    lean_dec_ref(v_inst_4786_);
    v_getEnv_4791_ = lean_ctor_get(v_inst_4787_, 0);
    lean_inc(v_getEnv_4791_);
    lean_dec_ref(v_inst_4787_);
    v_toPure_4792_ = lean_ctor_get(v_toApplicative_4789_, 1);
    lean_inc(v_toPure_4792_);
    lean_dec_ref(v_toApplicative_4789_);
    v___f_4793_ = lean_alloc_closure(
        l_Lean_getReducibilityStatus___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4793_, 0, v_declName_4788_);
    lean_closure_set(v___f_4793_, 1, v_toPure_4792_);
    v___x_4794_ = lean_apply_4(
        v_toBind_4790_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4791_,
        v___f_4793_,
    );
    return v___x_4794_;
}
pub unsafe fn l_Lean_getReducibilityStatus(
    mut v_m_4795_: *mut LeanObject,
    mut v_inst_4796_: *mut LeanObject,
    mut v_inst_4797_: *mut LeanObject,
    mut v_declName_4798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4799_: *mut LeanObject = core::ptr::null_mut();
    v___x_4799_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4796_, v_inst_4797_, v_declName_4798_);
    return v___x_4799_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg___lam__0(
    mut v_declName_4800_: *mut LeanObject,
    mut v_s_4801_: u8,
    mut v_env_4802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4803_: u8 = 0;
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut LeanObject = core::ptr::null_mut();
    v___x_4803_ = 0;
    v___x_4804_ = lean_box(0);
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
    mut v_declName_4806_: *mut LeanObject,
    mut v_s_4807_: *mut LeanObject,
    mut v_env_4808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_4809_: u8 = 0;
    let mut v_res_4810_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_4809_ = (lean_unbox(v_s_4807_) as u8);
    v_res_4810_ = l_Lean_setReducibilityStatus___redArg___lam__0(
        v_declName_4806_,
        v_s_boxed_4809_,
        v_env_4808_,
    );
    return v_res_4810_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg(
    mut v_inst_4811_: *mut LeanObject,
    mut v_declName_4812_: *mut LeanObject,
    mut v_s_4813_: u8,
) -> *mut LeanObject {
    let mut v_modifyEnv_4814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut LeanObject = core::ptr::null_mut();
    v_modifyEnv_4814_ = lean_ctor_get(v_inst_4811_, 1);
    lean_inc(v_modifyEnv_4814_);
    lean_dec_ref(v_inst_4811_);
    v___x_4815_ = lean_box((v_s_4813_) as usize);
    v___f_4816_ = lean_alloc_closure(
        l_Lean_setReducibilityStatus___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4816_, 0, v_declName_4812_);
    lean_closure_set(v___f_4816_, 1, v___x_4815_);
    v___x_4817_ = lean_apply_1(v_modifyEnv_4814_, v___f_4816_);
    return v___x_4817_;
}
pub unsafe fn l_Lean_setReducibilityStatus___redArg___boxed(
    mut v_inst_4818_: *mut LeanObject,
    mut v_declName_4819_: *mut LeanObject,
    mut v_s_4820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_4821_: u8 = 0;
    let mut v_res_4822_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_4821_ = (lean_unbox(v_s_4820_) as u8);
    v_res_4822_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4818_, v_declName_4819_, v_s_boxed_4821_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_setReducibilityStatus(
    mut v_m_4823_: *mut LeanObject,
    mut v_inst_4824_: *mut LeanObject,
    mut v_declName_4825_: *mut LeanObject,
    mut v_s_4826_: u8,
) -> *mut LeanObject {
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Lean_setReducibilityStatus___redArg(v_inst_4824_, v_declName_4825_, v_s_4826_);
    return v___x_4827_;
}
pub unsafe fn l_Lean_setReducibilityStatus___boxed(
    mut v_m_4828_: *mut LeanObject,
    mut v_inst_4829_: *mut LeanObject,
    mut v_declName_4830_: *mut LeanObject,
    mut v_s_4831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_boxed_4832_: u8 = 0;
    let mut v_res_4833_: *mut LeanObject = core::ptr::null_mut();
    v_s_boxed_4832_ = (lean_unbox(v_s_4831_) as u8);
    v_res_4833_ =
        l_Lean_setReducibilityStatus(v_m_4828_, v_inst_4829_, v_declName_4830_, v_s_boxed_4832_);
    return v_res_4833_;
}
pub unsafe fn l_Lean_setReducibleAttribute___redArg(
    mut v_inst_4834_: *mut LeanObject,
    mut v_declName_4835_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4836_: u8 = 0;
    let mut v___x_4837_: *mut LeanObject = core::ptr::null_mut();
    v___x_4836_ = 0;
    v___x_4837_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4834_, v_declName_4835_, v___x_4836_);
    return v___x_4837_;
}
pub unsafe fn l_Lean_setReducibleAttribute(
    mut v_m_4838_: *mut LeanObject,
    mut v_inst_4839_: *mut LeanObject,
    mut v_declName_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4841_: *mut LeanObject = core::ptr::null_mut();
    v___x_4841_ = l_Lean_setReducibleAttribute___redArg(v_inst_4839_, v_declName_4840_);
    return v___x_4841_;
}
pub unsafe fn l_Lean_isReducible___redArg___lam__0(
    mut v_toPure_4842_: *mut LeanObject,
    mut v_____do__lift_4843_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4843_ == 0 {
        let mut v___x_4844_: u8 = 0;
        let mut v___x_4845_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4846_: *mut LeanObject = core::ptr::null_mut();
        v___x_4844_ = 1;
        v___x_4845_ = lean_box((v___x_4844_) as usize);
        v___x_4846_ = lean_apply_2(v_toPure_4842_, lean_box(0), v___x_4845_);
        return v___x_4846_;
    } else {
        let mut v___x_4847_: u8 = 0;
        let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4849_: *mut LeanObject = core::ptr::null_mut();
        v___x_4847_ = 0;
        v___x_4848_ = lean_box((v___x_4847_) as usize);
        v___x_4849_ = lean_apply_2(v_toPure_4842_, lean_box(0), v___x_4848_);
        return v___x_4849_;
    }
}
pub unsafe fn l_Lean_isReducible___redArg___lam__0___boxed(
    mut v_toPure_4850_: *mut LeanObject,
    mut v_____do__lift_4851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_47__boxed_4852_: u8 = 0;
    let mut v_res_4853_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_47__boxed_4852_ = (lean_unbox(v_____do__lift_4851_) as u8);
    v_res_4853_ =
        l_Lean_isReducible___redArg___lam__0(v_toPure_4850_, v_____do__lift_47__boxed_4852_);
    return v_res_4853_;
}
pub unsafe fn l_Lean_isReducible___redArg(
    mut v_inst_4854_: *mut LeanObject,
    mut v_inst_4855_: *mut LeanObject,
    mut v_declName_4856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4857_ = lean_ctor_get(v_inst_4854_, 0);
    v_toBind_4858_ = lean_ctor_get(v_inst_4854_, 1);
    lean_inc(v_toBind_4858_);
    v_toPure_4859_ = lean_ctor_get(v_toApplicative_4857_, 1);
    lean_inc(v_toPure_4859_);
    v___x_4860_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4854_, v_inst_4855_, v_declName_4856_);
    v___f_4861_ = lean_alloc_closure(
        l_Lean_isReducible___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4861_, 0, v_toPure_4859_);
    v___x_4862_ = lean_apply_4(
        v_toBind_4858_,
        lean_box(0),
        lean_box(0),
        v___x_4860_,
        v___f_4861_,
    );
    return v___x_4862_;
}
pub unsafe fn l_Lean_isReducible(
    mut v_m_4863_: *mut LeanObject,
    mut v_inst_4864_: *mut LeanObject,
    mut v_inst_4865_: *mut LeanObject,
    mut v_declName_4866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    v___x_4867_ = l_Lean_isReducible___redArg(v_inst_4864_, v_inst_4865_, v_declName_4866_);
    return v___x_4867_;
}
pub unsafe fn l_Lean_isIrreducible___redArg___lam__0(
    mut v_toPure_4868_: *mut LeanObject,
    mut v_____do__lift_4869_: u8,
) -> *mut LeanObject {
    if v_____do__lift_4869_ == 2 {
        let mut v___x_4870_: u8 = 0;
        let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
        v___x_4870_ = 1;
        v___x_4871_ = lean_box((v___x_4870_) as usize);
        v___x_4872_ = lean_apply_2(v_toPure_4868_, lean_box(0), v___x_4871_);
        return v___x_4872_;
    } else {
        let mut v___x_4873_: u8 = 0;
        let mut v___x_4874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
        v___x_4873_ = 0;
        v___x_4874_ = lean_box((v___x_4873_) as usize);
        v___x_4875_ = lean_apply_2(v_toPure_4868_, lean_box(0), v___x_4874_);
        return v___x_4875_;
    }
}
pub unsafe fn l_Lean_isIrreducible___redArg___lam__0___boxed(
    mut v_toPure_4876_: *mut LeanObject,
    mut v_____do__lift_4877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_47__boxed_4878_: u8 = 0;
    let mut v_res_4879_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_47__boxed_4878_ = (lean_unbox(v_____do__lift_4877_) as u8);
    v_res_4879_ =
        l_Lean_isIrreducible___redArg___lam__0(v_toPure_4876_, v_____do__lift_47__boxed_4878_);
    return v_res_4879_;
}
pub unsafe fn l_Lean_isIrreducible___redArg(
    mut v_inst_4880_: *mut LeanObject,
    mut v_inst_4881_: *mut LeanObject,
    mut v_declName_4882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4883_ = lean_ctor_get(v_inst_4880_, 0);
    v_toBind_4884_ = lean_ctor_get(v_inst_4880_, 1);
    lean_inc(v_toBind_4884_);
    v_toPure_4885_ = lean_ctor_get(v_toApplicative_4883_, 1);
    lean_inc(v_toPure_4885_);
    v___x_4886_ =
        l_Lean_getReducibilityStatus___redArg(v_inst_4880_, v_inst_4881_, v_declName_4882_);
    v___f_4887_ = lean_alloc_closure(
        l_Lean_isIrreducible___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_4887_, 0, v_toPure_4885_);
    v___x_4888_ = lean_apply_4(
        v_toBind_4884_,
        lean_box(0),
        lean_box(0),
        v___x_4886_,
        v___f_4887_,
    );
    return v___x_4888_;
}
pub unsafe fn l_Lean_isIrreducible(
    mut v_m_4889_: *mut LeanObject,
    mut v_inst_4890_: *mut LeanObject,
    mut v_inst_4891_: *mut LeanObject,
    mut v_declName_4892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    v___x_4893_ = l_Lean_isIrreducible___redArg(v_inst_4890_, v_inst_4891_, v_declName_4892_);
    return v___x_4893_;
}
pub unsafe fn l_Lean_isImplicitReducibleCore(
    mut v_env_4894_: *mut LeanObject,
    mut v_declName_4895_: *mut LeanObject,
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
    mut v_env_4899_: *mut LeanObject,
    mut v_declName_4900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4901_: u8 = 0;
    let mut v_r_4902_: *mut LeanObject = core::ptr::null_mut();
    v_res_4901_ = l_Lean_isImplicitReducibleCore(v_env_4899_, v_declName_4900_);
    v_r_4902_ = lean_box((v_res_4901_) as usize);
    return v_r_4902_;
}
pub unsafe fn l_Lean_isImplicitReducible___redArg___lam__0(
    mut v_declName_4903_: *mut LeanObject,
    mut v_toPure_4904_: *mut LeanObject,
    mut v_____do__lift_4905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4906_: u8 = 0;
    let mut v___x_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    v___x_4906_ = l_Lean_isImplicitReducibleCore(v_____do__lift_4905_, v_declName_4903_);
    v___x_4907_ = lean_box((v___x_4906_) as usize);
    v___x_4908_ = lean_apply_2(v_toPure_4904_, lean_box(0), v___x_4907_);
    return v___x_4908_;
}
pub unsafe fn l_Lean_isImplicitReducible___redArg(
    mut v_inst_4909_: *mut LeanObject,
    mut v_inst_4910_: *mut LeanObject,
    mut v_declName_4911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_4912_ = lean_ctor_get(v_inst_4909_, 0);
    lean_inc_ref(v_toApplicative_4912_);
    v_toBind_4913_ = lean_ctor_get(v_inst_4909_, 1);
    lean_inc(v_toBind_4913_);
    lean_dec_ref(v_inst_4909_);
    v_getEnv_4914_ = lean_ctor_get(v_inst_4910_, 0);
    lean_inc(v_getEnv_4914_);
    lean_dec_ref(v_inst_4910_);
    v_toPure_4915_ = lean_ctor_get(v_toApplicative_4912_, 1);
    lean_inc(v_toPure_4915_);
    lean_dec_ref(v_toApplicative_4912_);
    v___f_4916_ = lean_alloc_closure(
        l_Lean_isImplicitReducible___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_4916_, 0, v_declName_4911_);
    lean_closure_set(v___f_4916_, 1, v_toPure_4915_);
    v___x_4917_ = lean_apply_4(
        v_toBind_4913_,
        lean_box(0),
        lean_box(0),
        v_getEnv_4914_,
        v___f_4916_,
    );
    return v___x_4917_;
}
pub unsafe fn l_Lean_isImplicitReducible(
    mut v_m_4918_: *mut LeanObject,
    mut v_inst_4919_: *mut LeanObject,
    mut v_inst_4920_: *mut LeanObject,
    mut v_declName_4921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4922_: *mut LeanObject = core::ptr::null_mut();
    v___x_4922_ = l_Lean_isImplicitReducible___redArg(v_inst_4919_, v_inst_4920_, v_declName_4921_);
    return v___x_4922_;
}
pub unsafe fn l_Lean_isInstanceReducibleCore(
    mut v_env_4923_: *mut LeanObject,
    mut v_declName_4924_: *mut LeanObject,
) -> u8 {
    let mut v___x_4925_: u8 = 0;
    v___x_4925_ = l_Lean_isImplicitReducibleCore(v_env_4923_, v_declName_4924_);
    return v___x_4925_;
}
pub unsafe fn l_Lean_isInstanceReducibleCore___boxed(
    mut v_env_4926_: *mut LeanObject,
    mut v_declName_4927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4928_: u8 = 0;
    let mut v_r_4929_: *mut LeanObject = core::ptr::null_mut();
    v_res_4928_ = l_Lean_isInstanceReducibleCore(v_env_4926_, v_declName_4927_);
    v_r_4929_ = lean_box((v_res_4928_) as usize);
    return v_r_4929_;
}
pub unsafe fn l_Lean_isInstanceReducible___redArg(
    mut v_inst_4930_: *mut LeanObject,
    mut v_inst_4931_: *mut LeanObject,
    mut v_declName_4932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    v___x_4933_ = l_Lean_isImplicitReducible___redArg(v_inst_4930_, v_inst_4931_, v_declName_4932_);
    return v___x_4933_;
}
pub unsafe fn l_Lean_isInstanceReducible(
    mut v_m_4934_: *mut LeanObject,
    mut v_inst_4935_: *mut LeanObject,
    mut v_inst_4936_: *mut LeanObject,
    mut v_declName_4937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    v___x_4938_ = l_Lean_isImplicitReducible___redArg(v_inst_4935_, v_inst_4936_, v_declName_4937_);
    return v___x_4938_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute___redArg(
    mut v_inst_4939_: *mut LeanObject,
    mut v_declName_4940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4941_: u8 = 0;
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    v___x_4941_ = 2;
    v___x_4942_ =
        l_Lean_setReducibilityStatus___redArg(v_inst_4939_, v_declName_4940_, v___x_4941_);
    return v___x_4942_;
}
pub unsafe fn l_Lean_setIrreducibleAttribute(
    mut v_m_4943_: *mut LeanObject,
    mut v_inst_4944_: *mut LeanObject,
    mut v_declName_4945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    v___x_4946_ = l_Lean_setIrreducibleAttribute___redArg(v_inst_4944_, v_declName_4945_);
    return v___x_4946_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ReducibilityAttrs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedReducibilityStatus_default =
        _init_l_Lean_instInhabitedReducibilityStatus_default();
    l_Lean_instInhabitedReducibilityStatus = _init_l_Lean_instInhabitedReducibilityStatus();
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_1725919122____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reducibilityCoreExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_reducibilityCoreExt);
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3557922905____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_reducibilityExtraExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_reducibilityExtraExt);
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_3530019704____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_allowUnsafeReducibility = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_allowUnsafeReducibility);
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_562565324____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_4118757939____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_2994861043____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_448179520____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ReducibilityAttrs_0__Lean_initFn_00___x40_Lean_ReducibilityAttrs_598760241____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ReducibilityAttrs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ReducibilityAttrs(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ReducibilityAttrs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ReducibilityAttrs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ReducibilityAttrs(builtin);
}
