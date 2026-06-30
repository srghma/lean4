// Lean compiler output
// Module: Lean.Meta.Tactic.FunIndInfo
// Imports: Lean.Meta.Basic Lean.ReservedNameAction
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_array_to_list,
    lean_array_uget_borrowed, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_length, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Format::Basic::l_Std_Format_fill;
use crate::r#gen::Init::Data::Repr::{l_Bool_repr___redArg, l_Repr_addAppParen};
use crate::r#gen::Init::Meta::Defs::l_Lean_Name_reprPrec;
use crate::r#gen::Init::Prelude::{l_Lean_Name_append, l_Lean_replaceRef};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instInhabitedCoreM___lam__0___boxed, l_Lean_Exception_isRuntime,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_MapDeclarationExtension_contains___redArg,
    l_Lean_MapDeclarationExtension_find_x3f___redArg,
    l_Lean_MapDeclarationExtension_insert___redArg, l_Lean_mkMapDeclarationExtension___redArg,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::{
    l_Lean_Exception_isInterrupt, l_Lean_unknownIdentifierMessageTag,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::{
    initialize_Lean_ReservedNameAction, l_Lean_realizeGlobalConstNoOverloadCore,
    runtime_initialize_Lean_ReservedNameAction,
};
pub static l_Lean_Meta_instBEqFunIndParamKind___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_instBEqFunIndParamKind_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instBEqFunIndParamKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqFunIndParamKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instBEqFunIndParamKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instBEqFunIndParamKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 70, 117, 110, 73, 110, 100, 80, 97, 114, 97,
        109, 75, 105, 110, 100, 46, 100, 114, 111, 112, 112, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 70, 117, 110, 73, 110, 100, 80, 97, 114, 97,
        109, 75, 105, 110, 100, 46, 112, 97, 114, 97, 109, 0,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value:
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 70, 117, 110, 73, 110, 100, 80, 97, 114, 97,
        109, 75, 105, 110, 100, 46, 116, 97, 114, 103, 101, 116, 0,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprFunIndParamKind_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndParamKind___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Lean_Meta_instReprFunIndParamKind_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_instReprFunIndParamKind___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instReprFunIndParamKind: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndParamKind___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedFunIndParamKind_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedFunIndParamKind: u8 = 0;
pub static l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value:
    leanh::LeanCtorObject<4> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4
            + 0) as u16,
        other: 4,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedFunIndInfo_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedFunIndInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedFunIndInfo_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value:
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
    m_data: [35, 91, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value:
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
    m_data: [44, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value:
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
        l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__1_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value:
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
        core::ptr::addr_of!(
            l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2_value
        ) as *mut leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value:
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
    m_data: [93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value:
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
        l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value:
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
        l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [35, 91, 93, 0],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value:
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
        l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__9_value
    ) as *mut leanh::LeanObject],
};
static mut l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value:
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
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [102, 117, 110, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value:
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
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [102, 117, 110, 73, 110, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__8_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [108, 101, 118, 101, 108, 77, 97, 115, 107, 0],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [112, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__14_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value:
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
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__17_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_instReprFunIndInfo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprFunIndInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprFunIndInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_instReprFunIndInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprFunIndInfo___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [102, 117, 110, 73, 110, 100, 73, 110, 102, 111, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9442000787290171069 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [0 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_funIndInfoExt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_getFunInductName___closed__0_value: leanh::LeanStringObject<7> =
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
        m_data: [105, 110, 100, 117, 99, 116, 0],
    };
static mut l_Lean_Meta_getFunInductName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunInductName___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__0_value)
                as *mut leanh::LeanObject,
            10500474214150955933 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getFunInductName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunInductName___closed__2_value: leanh::LeanStringObject<17> =
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
            105, 110, 100, 117, 99, 116, 95, 117, 110, 102, 111, 108, 100, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Meta_getFunInductName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunInductName___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__2_value)
                as *mut leanh::LeanObject,
            17634377603253611714 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getFunInductName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunInductName___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunCasesName___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [102, 117, 110, 95, 99, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Meta_getFunCasesName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunCasesName___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__0_value)
                as *mut leanh::LeanObject,
            13921216008602039104 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getFunCasesName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunCasesName___closed__2_value: leanh::LeanStringObject<20> =
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
            102, 117, 110, 95, 99, 97, 115, 101, 115, 95, 117, 110, 102, 111, 108, 100, 105, 110,
            103, 0,
        ],
    };
static mut l_Lean_Meta_getFunCasesName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getFunCasesName___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__2_value)
                as *mut leanh::LeanObject,
            13431374904016565164 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getFunCasesName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getFunCasesName___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getMutualInductName___closed__0_value: leanh::LeanStringObject<14> =
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
        m_data: [
            109, 117, 116, 117, 97, 108, 95, 105, 110, 100, 117, 99, 116, 0,
        ],
    };
static mut l_Lean_Meta_getMutualInductName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getMutualInductName___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__0_value)
                as *mut leanh::LeanObject,
            12046688123818169125 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getMutualInductName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getMutualInductName___closed__2_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            109, 117, 116, 117, 97, 108, 95, 105, 110, 100, 117, 99, 116, 95, 117, 110, 102, 111,
            108, 100, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_Meta_getMutualInductName___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_getMutualInductName___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__2_value)
                as *mut leanh::LeanObject,
            8515751793234623186 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_getMutualInductName___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getMutualInductName___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value:
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
    m_fun: l_Lean_Core_instInhabitedCoreM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_setFunIndInfo___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_setFunIndInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_setFunIndInfo___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_setFunIndInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_setFunIndInfo___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_setFunIndInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_setFunIndInfo___closed__3_value: leanh::LeanStringObject<28> =
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 70, 117, 110,
            73, 110, 100, 73, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Meta_setFunIndInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_setFunIndInfo___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_setFunIndInfo___closed__4_value: leanh::LeanStringObject<24> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 115, 101, 116, 70, 117, 110, 73, 110, 100,
            73, 110, 102, 111, 0,
        ],
    };
static mut l_Lean_Meta_setFunIndInfo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_setFunIndInfo___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_setFunIndInfo___closed__5_value: leanh::LeanStringObject<144> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 144,
        m_capacity: 144,
        m_length: 143,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 33, 40, 102, 117, 110, 73, 110, 100, 73, 110, 102, 111, 69, 120, 116, 46,
            99, 111, 110, 116, 97, 105, 110, 115, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102,
            116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105,
            99, 46, 70, 117, 110, 73, 110, 100, 73, 110, 102, 111, 46, 57, 57, 50, 52, 56, 51, 48,
            55, 56, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 57, 46, 48, 32,
            41, 32, 102, 117, 110, 73, 110, 100, 73, 110, 102, 111, 46, 102, 117, 110, 73, 110,
            100, 78, 97, 109, 101, 41, 10, 32, 32, 0,
        ],
    };
static mut l_Lean_Meta_setFunIndInfo___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_setFunIndInfo___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_setFunIndInfo___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_setFunIndInfo___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorIdx(
    mut v_x_1058_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1058_ {
        0 => {
            let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1059_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1059_;
        }
        1 => {
            let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1060_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1060_;
        }
        _ => {
            let mut v___x_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1061_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1061_;
        }
    }
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorIdx___boxed(
    mut v_x_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1063_: u8 = 0;
    let mut v_res_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1063_ = (leanh::lean_unbox(v_x_1062_) as u8);
    v_res_1064_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_boxed_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_toCtorIdx(
    mut v_x_1065_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1066_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_1065_);
    return v___x_1066_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_toCtorIdx___boxed(
    mut v_x_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1068_: u8 = 0;
    let mut v_res_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1068_ = (leanh::lean_unbox(v_x_1067_) as u8);
    v_res_1069_ = l_Lean_Meta_FunIndParamKind_toCtorIdx(v_x_4__boxed_1068_);
    return v_res_1069_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorElim___redArg(
    mut v_k_1070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1070_);
    return v_k_1070_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorElim___redArg___boxed(
    mut v_k_1071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Lean_Meta_FunIndParamKind_ctorElim___redArg(v_k_1071_);
    leanh::lean_dec(v_k_1071_);
    return v_res_1072_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorElim(
    mut v_motive_1073_: *mut leanh::LeanObject,
    mut v_ctorIdx_1074_: *mut leanh::LeanObject,
    mut v_t_1075_: u8,
    mut v_h_1076_: *mut leanh::LeanObject,
    mut v_k_1077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1077_);
    return v_k_1077_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_ctorElim___boxed(
    mut v_motive_1078_: *mut leanh::LeanObject,
    mut v_ctorIdx_1079_: *mut leanh::LeanObject,
    mut v_t_1080_: *mut leanh::LeanObject,
    mut v_h_1081_: *mut leanh::LeanObject,
    mut v_k_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1083_: u8 = 0;
    let mut v_res_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1083_ = (leanh::lean_unbox(v_t_1080_) as u8);
    v_res_1084_ = l_Lean_Meta_FunIndParamKind_ctorElim(
        v_motive_1078_,
        v_ctorIdx_1079_,
        v_t_boxed_1083_,
        v_h_1081_,
        v_k_1082_,
    );
    leanh::lean_dec(v_k_1082_);
    leanh::lean_dec(v_ctorIdx_1079_);
    return v_res_1084_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(
    mut v_dropped_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_dropped_1085_);
    return v_dropped_1085_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_dropped_elim___redArg___boxed(
    mut v_dropped_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_Lean_Meta_FunIndParamKind_dropped_elim___redArg(v_dropped_1086_);
    leanh::lean_dec(v_dropped_1086_);
    return v_res_1087_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_dropped_elim(
    mut v_motive_1088_: *mut leanh::LeanObject,
    mut v_t_1089_: u8,
    mut v_h_1090_: *mut leanh::LeanObject,
    mut v_dropped_1091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_dropped_1091_);
    return v_dropped_1091_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_dropped_elim___boxed(
    mut v_motive_1092_: *mut leanh::LeanObject,
    mut v_t_1093_: *mut leanh::LeanObject,
    mut v_h_1094_: *mut leanh::LeanObject,
    mut v_dropped_1095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1096_: u8 = 0;
    let mut v_res_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1096_ = (leanh::lean_unbox(v_t_1093_) as u8);
    v_res_1097_ = l_Lean_Meta_FunIndParamKind_dropped_elim(
        v_motive_1092_,
        v_t_boxed_1096_,
        v_h_1094_,
        v_dropped_1095_,
    );
    leanh::lean_dec(v_dropped_1095_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_param_elim___redArg(
    mut v_param_1098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_param_1098_);
    return v_param_1098_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_param_elim___redArg___boxed(
    mut v_param_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1100_ = l_Lean_Meta_FunIndParamKind_param_elim___redArg(v_param_1099_);
    leanh::lean_dec(v_param_1099_);
    return v_res_1100_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_param_elim(
    mut v_motive_1101_: *mut leanh::LeanObject,
    mut v_t_1102_: u8,
    mut v_h_1103_: *mut leanh::LeanObject,
    mut v_param_1104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_param_1104_);
    return v_param_1104_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_param_elim___boxed(
    mut v_motive_1105_: *mut leanh::LeanObject,
    mut v_t_1106_: *mut leanh::LeanObject,
    mut v_h_1107_: *mut leanh::LeanObject,
    mut v_param_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1109_: u8 = 0;
    let mut v_res_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1109_ = (leanh::lean_unbox(v_t_1106_) as u8);
    v_res_1110_ = l_Lean_Meta_FunIndParamKind_param_elim(
        v_motive_1105_,
        v_t_boxed_1109_,
        v_h_1107_,
        v_param_1108_,
    );
    leanh::lean_dec(v_param_1108_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_target_elim___redArg(
    mut v_target_1111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_target_1111_);
    return v_target_1111_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_target_elim___redArg___boxed(
    mut v_target_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1113_ = l_Lean_Meta_FunIndParamKind_target_elim___redArg(v_target_1112_);
    leanh::lean_dec(v_target_1112_);
    return v_res_1113_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_target_elim(
    mut v_motive_1114_: *mut leanh::LeanObject,
    mut v_t_1115_: u8,
    mut v_h_1116_: *mut leanh::LeanObject,
    mut v_target_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_target_1117_);
    return v_target_1117_;
}
pub unsafe fn l_Lean_Meta_FunIndParamKind_target_elim___boxed(
    mut v_motive_1118_: *mut leanh::LeanObject,
    mut v_t_1119_: *mut leanh::LeanObject,
    mut v_h_1120_: *mut leanh::LeanObject,
    mut v_target_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1122_: u8 = 0;
    let mut v_res_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1122_ = (leanh::lean_unbox(v_t_1119_) as u8);
    v_res_1123_ = l_Lean_Meta_FunIndParamKind_target_elim(
        v_motive_1118_,
        v_t_boxed_1122_,
        v_h_1120_,
        v_target_1121_,
    );
    leanh::lean_dec(v_target_1121_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_Meta_instBEqFunIndParamKind_beq(mut v_x_1124_: u8, mut v_y_1125_: u8) -> u8 {
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: u8 = 0;
    v___x_1126_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_x_1124_);
    v___x_1127_ = l_Lean_Meta_FunIndParamKind_ctorIdx(v_y_1125_);
    v___x_1128_ = lean_nat_dec_eq(v___x_1126_, v___x_1127_);
    leanh::lean_dec(v___x_1127_);
    leanh::lean_dec(v___x_1126_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_Meta_instBEqFunIndParamKind_beq___boxed(
    mut v_x_1129_: *mut leanh::LeanObject,
    mut v_y_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_1131_: u8 = 0;
    let mut v_y_18__boxed_1132_: u8 = 0;
    let mut v_res_1133_: u8 = 0;
    let mut v_r_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1131_ = (leanh::lean_unbox(v_x_1129_) as u8);
    v_y_18__boxed_1132_ = (leanh::lean_unbox(v_y_1130_) as u8);
    v_res_1133_ = l_Lean_Meta_instBEqFunIndParamKind_beq(v_x_17__boxed_1131_, v_y_18__boxed_1132_);
    v_r_1134_ = leanh::lean_box((v_res_1133_) as usize);
    return v_r_1134_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = leanh::lean_unsigned_to_nat(2);
    v___x_1147_ = lean_nat_to_int(v___x_1146_);
    return v___x_1147_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1148_ = leanh::lean_unsigned_to_nat(1);
    v___x_1149_ = lean_nat_to_int(v___x_1148_);
    return v___x_1149_;
}
pub unsafe fn l_Lean_Meta_instReprFunIndParamKind_repr(
    mut v_x_1150_: u8,
    mut v_prec_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: u8 = 0;
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: u8 = 0;
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: u8 = 0;
    let mut v___x_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1150_ {
                0 => {
                    v___x_1173_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1174_ = lean_nat_dec_le(v___x_1173_, v_prec_1151_);
                    if v___x_1174_ == 0 {
                        v___x_1175_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6,
                        );
                        v___y_1153_ = v___x_1175_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1176_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7,
                        );
                        v___y_1153_ = v___x_1176_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1177_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1178_ = lean_nat_dec_le(v___x_1177_, v_prec_1151_);
                    if v___x_1178_ == 0 {
                        v___x_1179_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6,
                        );
                        v___y_1160_ = v___x_1179_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1180_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7,
                        );
                        v___y_1160_ = v___x_1180_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1181_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1182_ = lean_nat_dec_le(v___x_1181_, v_prec_1151_);
                    if v___x_1182_ == 0 {
                        v___x_1183_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__6,
                        );
                        v___y_1167_ = v___x_1183_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1184_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprFunIndParamKind_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprFunIndParamKind_repr___closed__7,
                        );
                        v___y_1167_ = v___x_1184_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1154_ = l_Lean_Meta_instReprFunIndParamKind_repr___closed__1;
                leanh::lean_inc(v___y_1153_);
                v___x_1155_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1155_, 0, v___y_1153_);
                leanh::lean_ctor_set(v___x_1155_, 1, v___x_1154_);
                v___x_1156_ = 0;
                v___x_1157_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1157_, 0, v___x_1155_);
                leanh::lean_ctor_set_uint8(
                    v___x_1157_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1156_,
                );
                v___x_1158_ = l_Repr_addAppParen(v___x_1157_, v_prec_1151_);
                return v___x_1158_;
            }
            2 => {
                v___x_1161_ = l_Lean_Meta_instReprFunIndParamKind_repr___closed__3;
                leanh::lean_inc(v___y_1160_);
                v___x_1162_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1162_, 0, v___y_1160_);
                leanh::lean_ctor_set(v___x_1162_, 1, v___x_1161_);
                v___x_1163_ = 0;
                v___x_1164_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1164_, 0, v___x_1162_);
                leanh::lean_ctor_set_uint8(
                    v___x_1164_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1163_,
                );
                v___x_1165_ = l_Repr_addAppParen(v___x_1164_, v_prec_1151_);
                return v___x_1165_;
            }
            3 => {
                v___x_1168_ = l_Lean_Meta_instReprFunIndParamKind_repr___closed__5;
                leanh::lean_inc(v___y_1167_);
                v___x_1169_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1169_, 0, v___y_1167_);
                leanh::lean_ctor_set(v___x_1169_, 1, v___x_1168_);
                v___x_1170_ = 0;
                v___x_1171_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1171_, 0, v___x_1169_);
                leanh::lean_ctor_set_uint8(
                    v___x_1171_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1170_,
                );
                v___x_1172_ = l_Repr_addAppParen(v___x_1171_, v_prec_1151_);
                return v___x_1172_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReprFunIndParamKind_repr___boxed(
    mut v_x_1185_: *mut leanh::LeanObject,
    mut v_prec_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_1187_: u8 = 0;
    let mut v_res_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1187_ = (leanh::lean_unbox(v_x_1185_) as u8);
    v_res_1188_ = l_Lean_Meta_instReprFunIndParamKind_repr(v_x_177__boxed_1187_, v_prec_1186_);
    leanh::lean_dec(v_prec_1186_);
    return v_res_1188_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedFunIndParamKind_default() -> u8 {
    let mut v___x_1191_: u8 = 0;
    v___x_1191_ = 0;
    return v___x_1191_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedFunIndParamKind() -> u8 {
    let mut v___x_1192_: u8 = 0;
    v___x_1192_ = 0;
    return v___x_1192_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_instReprFunIndInfo_repr_spec__2(
    mut v_a_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = lean_nat_to_int(v_a_1200_);
    return v___x_1201_;
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(
    mut v_x_1202_: *mut leanh::LeanObject,
    mut v_x_1203_: *mut leanh::LeanObject,
    mut v_x_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1209_: u8 = 0;
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1204_) == 0 {
                    leanh::lean_dec(v_x_1202_);
                    return v_x_1203_;
                } else {
                    v_head_1205_ = leanh::lean_ctor_get(v_x_1204_, 0);
                    v_tail_1206_ = leanh::lean_ctor_get(v_x_1204_, 1);
                    v_isSharedCheck_1217_ = (!leanh::lean_is_exclusive(v_x_1204_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1208_ = v_x_1204_;
                        v_isShared_1209_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1206_);
                        leanh::lean_inc(v_head_1205_);
                        leanh::lean_dec(v_x_1204_);
                        v___x_1208_ = leanh::lean_box(0);
                        v_isShared_1209_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1202_);
                if v_isShared_1209_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1208_, 5);
                    leanh::lean_ctor_set(v___x_1208_, 1, v_x_1202_);
                    leanh::lean_ctor_set(v___x_1208_, 0, v_x_1203_);
                    v___x_1211_ = v___x_1208_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_x_1203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_x_1202_);
                    v___x_1211_ = v_reuseFailAlloc_1216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1212_ = (leanh::lean_unbox(v_head_1205_) as u8);
                leanh::lean_dec(v_head_1205_);
                v___x_1213_ = l_Bool_repr___redArg(v___x_1212_);
                v___x_1214_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1214_, 0, v___x_1211_);
                leanh::lean_ctor_set(v___x_1214_, 1, v___x_1213_);
                v_x_1203_ = v___x_1214_;
                v_x_1204_ = v_tail_1206_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(
    mut v_x_1218_: *mut leanh::LeanObject,
    mut v_x_1219_: *mut leanh::LeanObject,
    mut v_x_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1225_: u8 = 0;
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: u8 = 0;
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1220_) == 0 {
                    leanh::lean_dec(v_x_1218_);
                    return v_x_1219_;
                } else {
                    v_head_1221_ = leanh::lean_ctor_get(v_x_1220_, 0);
                    v_tail_1222_ = leanh::lean_ctor_get(v_x_1220_, 1);
                    v_isSharedCheck_1233_ = (!leanh::lean_is_exclusive(v_x_1220_)) as u8;
                    if v_isSharedCheck_1233_ == 0 {
                        v___x_1224_ = v_x_1220_;
                        v_isShared_1225_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1222_);
                        leanh::lean_inc(v_head_1221_);
                        leanh::lean_dec(v_x_1220_);
                        v___x_1224_ = leanh::lean_box(0);
                        v_isShared_1225_ = v_isSharedCheck_1233_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1218_);
                if v_isShared_1225_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1224_, 5);
                    leanh::lean_ctor_set(v___x_1224_, 1, v_x_1218_);
                    leanh::lean_ctor_set(v___x_1224_, 0, v_x_1219_);
                    v___x_1227_ = v___x_1224_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1232_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_x_1219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1232_, 1, v_x_1218_);
                    v___x_1227_ = v_reuseFailAlloc_1232_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1228_ = (leanh::lean_unbox(v_head_1221_) as u8);
                leanh::lean_dec(v_head_1221_);
                v___x_1229_ = l_Bool_repr___redArg(v___x_1228_);
                v___x_1230_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1230_, 0, v___x_1227_);
                leanh::lean_ctor_set(v___x_1230_, 1, v___x_1229_);
                v___x_1231_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2_spec__4(v_x_1218_, v___x_1230_, v_tail_1222_);
                return v___x_1231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(
    mut v_x_1234_: *mut leanh::LeanObject,
    mut v_x_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1234_) == 0 {
        let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1235_);
        v___x_1236_ = leanh::lean_box(0);
        return v___x_1236_;
    } else {
        let mut v_tail_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1237_ = leanh::lean_ctor_get(v_x_1234_, 1);
        if leanh::lean_obj_tag(v_tail_1237_) == 0 {
            let mut v_head_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1239_: u8 = 0;
            let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1235_);
            v_head_1238_ = leanh::lean_ctor_get(v_x_1234_, 0);
            leanh::lean_inc(v_head_1238_);
            leanh::lean_dec_ref_known(v_x_1234_, 2);
            v___x_1239_ = (leanh::lean_unbox(v_head_1238_) as u8);
            leanh::lean_dec(v_head_1238_);
            v___x_1240_ = l_Bool_repr___redArg(v___x_1239_);
            return v___x_1240_;
        } else {
            let mut v_head_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1242_: u8 = 0;
            let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1237_);
            v_head_1241_ = leanh::lean_ctor_get(v_x_1234_, 0);
            leanh::lean_inc(v_head_1241_);
            leanh::lean_dec_ref_known(v_x_1234_, 2);
            v___x_1242_ = (leanh::lean_unbox(v_head_1241_) as u8);
            leanh::lean_dec(v_head_1241_);
            v___x_1243_ = l_Bool_repr___redArg(v___x_1242_);
            v___x_1244_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0_spec__2(v_x_1235_, v___x_1243_, v_tail_1237_);
            return v___x_1244_;
        }
    }
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1253_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__0;
    v___x_1254_ = lean_string_length(v___x_1253_);
    return v___x_1254_;
}
pub unsafe fn _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5_once
        ),
        _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__5,
    );
    v___x_1256_ = lean_nat_to_int(v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(
    mut v_xs_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: u8 = 0;
    v___x_1265_ = lean_array_get_size(v_xs_1264_);
    v___x_1266_ = leanh::lean_unsigned_to_nat(0);
    v___x_1267_ = lean_nat_dec_eq(v___x_1265_, v___x_1266_);
    if v___x_1267_ == 0 {
        let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1268_ = lean_array_to_list(v_xs_1264_);
        v___x_1269_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3;
        v___x_1270_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0_spec__0(v___x_1268_, v___x_1269_);
        v___x_1271_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6,
        );
        v___x_1272_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7;
        v___x_1273_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1273_, 0, v___x_1272_);
        leanh::lean_ctor_set(v___x_1273_, 1, v___x_1270_);
        v___x_1274_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8;
        v___x_1275_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1275_, 0, v___x_1273_);
        leanh::lean_ctor_set(v___x_1275_, 1, v___x_1274_);
        v___x_1276_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1276_, 0, v___x_1271_);
        leanh::lean_ctor_set(v___x_1276_, 1, v___x_1275_);
        v___x_1277_ = l_Std_Format_fill(v___x_1276_);
        return v___x_1277_;
    } else {
        let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1264_);
        v___x_1278_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10;
        return v___x_1278_;
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(
    mut v_x_1279_: *mut leanh::LeanObject,
    mut v_x_1280_: *mut leanh::LeanObject,
    mut v_x_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1286_: u8 = 0;
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1281_) == 0 {
                    leanh::lean_dec(v_x_1279_);
                    return v_x_1280_;
                } else {
                    v_head_1282_ = leanh::lean_ctor_get(v_x_1281_, 0);
                    v_tail_1283_ = leanh::lean_ctor_get(v_x_1281_, 1);
                    v_isSharedCheck_1295_ = (!leanh::lean_is_exclusive(v_x_1281_)) as u8;
                    if v_isSharedCheck_1295_ == 0 {
                        v___x_1285_ = v_x_1281_;
                        v_isShared_1286_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1283_);
                        leanh::lean_inc(v_head_1282_);
                        leanh::lean_dec(v_x_1281_);
                        v___x_1285_ = leanh::lean_box(0);
                        v_isShared_1286_ = v_isSharedCheck_1295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1279_);
                if v_isShared_1286_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1285_, 5);
                    leanh::lean_ctor_set(v___x_1285_, 1, v_x_1279_);
                    leanh::lean_ctor_set(v___x_1285_, 0, v_x_1280_);
                    v___x_1288_ = v___x_1285_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1294_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_x_1280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_x_1279_);
                    v___x_1288_ = v_reuseFailAlloc_1294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1289_ = leanh::lean_unsigned_to_nat(0);
                v___x_1290_ = (leanh::lean_unbox(v_head_1282_) as u8);
                leanh::lean_dec(v_head_1282_);
                v___x_1291_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_1290_, v___x_1289_);
                v___x_1292_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1292_, 0, v___x_1288_);
                leanh::lean_ctor_set(v___x_1292_, 1, v___x_1291_);
                v_x_1280_ = v___x_1292_;
                v_x_1281_ = v_tail_1283_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(
    mut v_x_1296_: *mut leanh::LeanObject,
    mut v_x_1297_: *mut leanh::LeanObject,
    mut v_x_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1303_: u8 = 0;
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: u8 = 0;
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1298_) == 0 {
                    leanh::lean_dec(v_x_1296_);
                    return v_x_1297_;
                } else {
                    v_head_1299_ = leanh::lean_ctor_get(v_x_1298_, 0);
                    v_tail_1300_ = leanh::lean_ctor_get(v_x_1298_, 1);
                    v_isSharedCheck_1312_ = (!leanh::lean_is_exclusive(v_x_1298_)) as u8;
                    if v_isSharedCheck_1312_ == 0 {
                        v___x_1302_ = v_x_1298_;
                        v_isShared_1303_ = v_isSharedCheck_1312_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1300_);
                        leanh::lean_inc(v_head_1299_);
                        leanh::lean_dec(v_x_1298_);
                        v___x_1302_ = leanh::lean_box(0);
                        v_isShared_1303_ = v_isSharedCheck_1312_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1296_);
                if v_isShared_1303_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1302_, 5);
                    leanh::lean_ctor_set(v___x_1302_, 1, v_x_1296_);
                    leanh::lean_ctor_set(v___x_1302_, 0, v_x_1297_);
                    v___x_1305_ = v___x_1302_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_x_1297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1311_, 1, v_x_1296_);
                    v___x_1305_ = v_reuseFailAlloc_1311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1306_ = leanh::lean_unsigned_to_nat(0);
                v___x_1307_ = (leanh::lean_unbox(v_head_1299_) as u8);
                leanh::lean_dec(v_head_1299_);
                v___x_1308_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___x_1307_, v___x_1306_);
                v___x_1309_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1309_, 0, v___x_1305_);
                leanh::lean_ctor_set(v___x_1309_, 1, v___x_1308_);
                v___x_1310_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5_spec__7(v_x_1296_, v___x_1309_, v_tail_1300_);
                return v___x_1310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(
    mut v___y_1313_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1314_ = leanh::lean_unsigned_to_nat(0);
    v___x_1315_ = l_Lean_Meta_instReprFunIndParamKind_repr(v___y_1313_, v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0___boxed(
    mut v___y_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_842__boxed_1317_: u8 = 0;
    let mut v_res_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_842__boxed_1317_ = (leanh::lean_unbox(v___y_1316_) as u8);
    v_res_1318_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___y_842__boxed_1317_);
    return v_res_1318_;
}
pub unsafe fn l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(
    mut v_x_1319_: *mut leanh::LeanObject,
    mut v_x_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1319_) == 0 {
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1320_);
        v___x_1321_ = leanh::lean_box(0);
        return v___x_1321_;
    } else {
        let mut v_tail_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1322_ = leanh::lean_ctor_get(v_x_1319_, 1);
        if leanh::lean_obj_tag(v_tail_1322_) == 0 {
            let mut v_head_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1324_: u8 = 0;
            let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1320_);
            v_head_1323_ = leanh::lean_ctor_get(v_x_1319_, 0);
            leanh::lean_inc(v_head_1323_);
            leanh::lean_dec_ref_known(v_x_1319_, 2);
            v___x_1324_ = (leanh::lean_unbox(v_head_1323_) as u8);
            leanh::lean_dec(v_head_1323_);
            v___x_1325_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_1324_);
            return v___x_1325_;
        } else {
            let mut v_head_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1327_: u8 = 0;
            let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1322_);
            v_head_1326_ = leanh::lean_ctor_get(v_x_1319_, 0);
            leanh::lean_inc(v_head_1326_);
            leanh::lean_dec_ref_known(v_x_1319_, 2);
            v___x_1327_ = (leanh::lean_unbox(v_head_1326_) as u8);
            leanh::lean_dec(v_head_1326_);
            v___x_1328_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2___lam__0(v___x_1327_);
            v___x_1329_ = l_List_foldl___at___00Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2_spec__5(v_x_1320_, v___x_1328_, v_tail_1322_);
            return v___x_1329_;
        }
    }
}
pub unsafe fn l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(
    mut v_xs_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    v___x_1331_ = lean_array_get_size(v_xs_1330_);
    v___x_1332_ = leanh::lean_unsigned_to_nat(0);
    v___x_1333_ = lean_nat_dec_eq(v___x_1331_, v___x_1332_);
    if v___x_1333_ == 0 {
        let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1334_ = lean_array_to_list(v_xs_1330_);
        v___x_1335_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__3;
        v___x_1336_ = l_Std_Format_joinSep___at___00Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1_spec__2(v___x_1334_, v___x_1335_);
        v___x_1337_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6
            ),
            core::ptr::addr_of_mut!(
                l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6_once
            ),
            _init_l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__6,
        );
        v___x_1338_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__7;
        v___x_1339_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1339_, 0, v___x_1338_);
        leanh::lean_ctor_set(v___x_1339_, 1, v___x_1336_);
        v___x_1340_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__8;
        v___x_1341_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1341_, 0, v___x_1339_);
        leanh::lean_ctor_set(v___x_1341_, 1, v___x_1340_);
        v___x_1342_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1342_, 0, v___x_1337_);
        leanh::lean_ctor_set(v___x_1342_, 1, v___x_1341_);
        v___x_1343_ = l_Std_Format_fill(v___x_1342_);
        return v___x_1343_;
    } else {
        let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_xs_1330_);
        v___x_1344_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__10;
        return v___x_1344_;
    }
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = leanh::lean_unsigned_to_nat(11);
    v___x_1359_ = lean_nat_to_int(v___x_1358_);
    return v___x_1359_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = leanh::lean_unsigned_to_nat(14);
    v___x_1364_ = lean_nat_to_int(v___x_1363_);
    return v___x_1364_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1368_ = leanh::lean_unsigned_to_nat(13);
    v___x_1369_ = lean_nat_to_int(v___x_1368_);
    return v___x_1369_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1373_ = leanh::lean_unsigned_to_nat(10);
    v___x_1374_ = lean_nat_to_int(v___x_1373_);
    return v___x_1374_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1376_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__0;
    v___x_1377_ = lean_string_length(v___x_1376_);
    return v___x_1377_;
}
pub unsafe fn _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1378_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__18,
    );
    v___x_1379_ = lean_nat_to_int(v___x_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Lean_Meta_instReprFunIndInfo_repr___redArg(
    mut v_x_1384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_funName_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndName_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelMask_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_funName_1385_ = leanh::lean_ctor_get(v_x_1384_, 0);
    leanh::lean_inc(v_funName_1385_);
    v_funIndName_1386_ = leanh::lean_ctor_get(v_x_1384_, 1);
    leanh::lean_inc(v_funIndName_1386_);
    v_levelMask_1387_ = leanh::lean_ctor_get(v_x_1384_, 2);
    leanh::lean_inc_ref(v_levelMask_1387_);
    v_params_1388_ = leanh::lean_ctor_get(v_x_1384_, 3);
    leanh::lean_inc_ref(v_params_1388_);
    leanh::lean_dec_ref(v_x_1384_);
    v___x_1389_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__5;
    v___x_1390_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__6;
    v___x_1391_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__7,
    );
    v___x_1392_ = leanh::lean_unsigned_to_nat(0);
    v___x_1393_ = l_Lean_Name_reprPrec(v_funName_1385_, v___x_1392_);
    v___x_1394_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1394_, 0, v___x_1391_);
    leanh::lean_ctor_set(v___x_1394_, 1, v___x_1393_);
    v___x_1395_ = 0;
    v___x_1396_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1396_, 0, v___x_1394_);
    leanh::lean_ctor_set_uint8(
        v___x_1396_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1395_,
    );
    v___x_1397_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1397_, 0, v___x_1390_);
    leanh::lean_ctor_set(v___x_1397_, 1, v___x_1396_);
    v___x_1398_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0___closed__2;
    v___x_1399_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1399_, 0, v___x_1397_);
    leanh::lean_ctor_set(v___x_1399_, 1, v___x_1398_);
    v___x_1400_ = leanh::lean_box(1);
    v___x_1401_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1401_, 0, v___x_1399_);
    leanh::lean_ctor_set(v___x_1401_, 1, v___x_1400_);
    v___x_1402_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__9;
    v___x_1403_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1403_, 0, v___x_1401_);
    leanh::lean_ctor_set(v___x_1403_, 1, v___x_1402_);
    v___x_1404_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1404_, 0, v___x_1403_);
    leanh::lean_ctor_set(v___x_1404_, 1, v___x_1389_);
    v___x_1405_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__10,
    );
    v___x_1406_ = l_Lean_Name_reprPrec(v_funIndName_1386_, v___x_1392_);
    v___x_1407_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1407_, 0, v___x_1405_);
    leanh::lean_ctor_set(v___x_1407_, 1, v___x_1406_);
    v___x_1408_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1408_, 0, v___x_1407_);
    leanh::lean_ctor_set_uint8(
        v___x_1408_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1395_,
    );
    v___x_1409_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1409_, 0, v___x_1404_);
    leanh::lean_ctor_set(v___x_1409_, 1, v___x_1408_);
    v___x_1410_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1410_, 0, v___x_1409_);
    leanh::lean_ctor_set(v___x_1410_, 1, v___x_1398_);
    v___x_1411_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1411_, 0, v___x_1410_);
    leanh::lean_ctor_set(v___x_1411_, 1, v___x_1400_);
    v___x_1412_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__12;
    v___x_1413_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1413_, 0, v___x_1411_);
    leanh::lean_ctor_set(v___x_1413_, 1, v___x_1412_);
    v___x_1414_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1414_, 0, v___x_1413_);
    leanh::lean_ctor_set(v___x_1414_, 1, v___x_1389_);
    v___x_1415_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__13,
    );
    v___x_1416_ =
        l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__0(v_levelMask_1387_);
    v___x_1417_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1417_, 0, v___x_1415_);
    leanh::lean_ctor_set(v___x_1417_, 1, v___x_1416_);
    v___x_1418_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1418_, 0, v___x_1417_);
    leanh::lean_ctor_set_uint8(
        v___x_1418_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1395_,
    );
    v___x_1419_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1419_, 0, v___x_1414_);
    leanh::lean_ctor_set(v___x_1419_, 1, v___x_1418_);
    v___x_1420_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1420_, 0, v___x_1419_);
    leanh::lean_ctor_set(v___x_1420_, 1, v___x_1398_);
    v___x_1421_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1421_, 0, v___x_1420_);
    leanh::lean_ctor_set(v___x_1421_, 1, v___x_1400_);
    v___x_1422_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__15;
    v___x_1423_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1423_, 0, v___x_1421_);
    leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
    v___x_1424_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1424_, 0, v___x_1423_);
    leanh::lean_ctor_set(v___x_1424_, 1, v___x_1389_);
    v___x_1425_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__16,
    );
    v___x_1426_ = l_Array_repr___at___00Lean_Meta_instReprFunIndInfo_repr_spec__1(v_params_1388_);
    v___x_1427_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1427_, 0, v___x_1425_);
    leanh::lean_ctor_set(v___x_1427_, 1, v___x_1426_);
    v___x_1428_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1428_, 0, v___x_1427_);
    leanh::lean_ctor_set_uint8(
        v___x_1428_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1395_,
    );
    v___x_1429_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1424_);
    leanh::lean_ctor_set(v___x_1429_, 1, v___x_1428_);
    v___x_1430_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19_once),
        _init_l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__19,
    );
    v___x_1431_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__20;
    v___x_1432_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    leanh::lean_ctor_set(v___x_1432_, 1, v___x_1429_);
    v___x_1433_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg___closed__21;
    v___x_1434_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1434_, 0, v___x_1432_);
    leanh::lean_ctor_set(v___x_1434_, 1, v___x_1433_);
    v___x_1435_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1430_);
    leanh::lean_ctor_set(v___x_1435_, 1, v___x_1434_);
    v___x_1436_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1436_, 0, v___x_1435_);
    leanh::lean_ctor_set_uint8(
        v___x_1436_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1395_,
    );
    return v___x_1436_;
}
pub unsafe fn l_Lean_Meta_instReprFunIndInfo_repr(
    mut v_x_1437_: *mut leanh::LeanObject,
    mut v_prec_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lean_Meta_instReprFunIndInfo_repr___redArg(v_x_1437_);
    return v___x_1439_;
}
pub unsafe fn l_Lean_Meta_instReprFunIndInfo_repr___boxed(
    mut v_x_1440_: *mut leanh::LeanObject,
    mut v_prec_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ = l_Lean_Meta_instReprFunIndInfo_repr(v_x_1440_, v_prec_1441_);
    leanh::lean_dec(v_prec_1441_);
    return v_res_1442_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(
    mut v_env_1445_: *mut leanh::LeanObject,
    mut v_as_1446_: *mut leanh::LeanObject,
    mut v_i_1447_: usize,
    mut v_stop_1448_: usize,
    mut v_b_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: usize = 0;
    let mut v___x_1453_: usize = 0;
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1455_ = lean_usize_dec_eq(v_i_1447_, v_stop_1448_);
                if v___x_1455_ == 0 {
                    v___x_1456_ = lean_array_uget_borrowed(v_as_1446_, v_i_1447_);
                    v_fst_1457_ = leanh::lean_ctor_get(v___x_1456_, 0);
                    leanh::lean_inc(v_fst_1457_);
                    leanh::lean_inc_ref(v_env_1445_);
                    v___x_1458_ =
                        l_Lean_Environment_contains(v_env_1445_, v_fst_1457_, v___x_1455_);
                    if v___x_1458_ == 0 {
                        v___y_1451_ = v_b_1449_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_1456_);
                        v___x_1459_ = lean_array_push(v_b_1449_, v___x_1456_);
                        v___y_1451_ = v___x_1459_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1445_);
                    return v_b_1449_;
                }
            }
            1 => {
                v___x_1452_ = 1usize;
                v___x_1453_ = lean_usize_add(v_i_1447_, v___x_1452_);
                v_i_1447_ = v___x_1453_;
                v_b_1449_ = v___y_1451_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1___boxed(
    mut v_env_1460_: *mut leanh::LeanObject,
    mut v_as_1461_: *mut leanh::LeanObject,
    mut v_i_1462_: *mut leanh::LeanObject,
    mut v_stop_1463_: *mut leanh::LeanObject,
    mut v_b_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1465_: usize = 0;
    let mut v_stop_boxed_1466_: usize = 0;
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1465_ = leanh::lean_unbox_usize(v_i_1462_);
    leanh::lean_dec(v_i_1462_);
    v_stop_boxed_1466_ = leanh::lean_unbox_usize(v_stop_1463_);
    leanh::lean_dec(v_stop_1463_);
    v_res_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_1460_, v_as_1461_, v_i_boxed_1465_, v_stop_boxed_1466_, v_b_1464_);
    leanh::lean_dec_ref(v_as_1461_);
    return v_res_1467_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(
    mut v_init_1468_: *mut leanh::LeanObject,
    mut v_x_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1469_) == 0 {
                    v_k_1470_ = leanh::lean_ctor_get(v_x_1469_, 1);
                    v_v_1471_ = leanh::lean_ctor_get(v_x_1469_, 2);
                    v_l_1472_ = leanh::lean_ctor_get(v_x_1469_, 3);
                    v_r_1473_ = leanh::lean_ctor_get(v_x_1469_, 4);
                    v___x_1474_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_1468_, v_l_1472_);
                    leanh::lean_inc(v_v_1471_);
                    leanh::lean_inc(v_k_1470_);
                    v___x_1475_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1475_, 0, v_k_1470_);
                    leanh::lean_ctor_set(v___x_1475_, 1, v_v_1471_);
                    v___x_1476_ = lean_array_push(v___x_1474_, v___x_1475_);
                    v_init_1468_ = v___x_1476_;
                    v_x_1469_ = v_r_1473_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1468_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_init_1478_: *mut leanh::LeanObject,
    mut v_x_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_1478_, v_x_1479_);
    leanh::lean_dec(v_x_1479_);
    return v_res_1480_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(
    mut v_env_1487_: *mut leanh::LeanObject,
    mut v_s_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    v___x_1489_ = leanh::lean_unsigned_to_nat(0);
    v___x_1490_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
    v___x_1491_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v___x_1490_, v_s_1488_);
    v___x_1492_ = lean_array_get_size(v___x_1491_);
    v___x_1493_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
    v___x_1494_ = lean_nat_dec_lt(v___x_1489_, v___x_1492_);
    if v___x_1494_ == 0 {
        let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_1491_);
        leanh::lean_dec_ref(v_env_1487_);
        v___x_1495_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
        return v___x_1495_;
    } else {
        let mut v___x_1496_: u8 = 0;
        v___x_1496_ = lean_nat_dec_le(v___x_1492_, v___x_1492_);
        if v___x_1496_ == 0 {
            if v___x_1494_ == 0 {
                let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v___x_1491_);
                leanh::lean_dec_ref(v_env_1487_);
                v___x_1497_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
                return v___x_1497_;
            } else {
                let mut v___x_1498_: usize = 0;
                let mut v___x_1499_: usize = 0;
                let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1498_ = 0usize;
                v___x_1499_ = lean_usize_of_nat(v___x_1492_);
                v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_1487_, v___x_1491_, v___x_1498_, v___x_1499_, v___x_1493_);
                leanh::lean_dec_ref(v___x_1491_);
                leanh::lean_inc_ref_n(v___x_1500_, 2);
                v___x_1501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1501_, 0, v___x_1500_);
                leanh::lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                leanh::lean_ctor_set(v___x_1501_, 2, v___x_1500_);
                return v___x_1501_;
            }
        } else {
            let mut v___x_1502_: usize = 0;
            let mut v___x_1503_: usize = 0;
            let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1502_ = 0usize;
            v___x_1503_ = lean_usize_of_nat(v___x_1492_);
            v___x_1504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__1(v_env_1487_, v___x_1491_, v___x_1502_, v___x_1503_, v___x_1493_);
            leanh::lean_dec_ref(v___x_1491_);
            leanh::lean_inc_ref_n(v___x_1504_, 2);
            v___x_1505_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_1505_, 0, v___x_1504_);
            leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
            leanh::lean_ctor_set(v___x_1505_, 2, v___x_1504_);
            return v___x_1505_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(
    mut v_env_1506_: *mut leanh::LeanObject,
    mut v_s_1507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1508_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_(v_env_1506_, v_s_1507_);
    leanh::lean_dec(v_s_1507_);
    return v_res_1508_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1520_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
    v___x_1521_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
    v___x_1522_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_;
    v___x_1523_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_1521_, v___x_1522_, v___f_1520_);
    return v___x_1523_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2____boxed(
    mut v_a_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1525_ = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
    return v_res_1525_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(
    mut v_init_1526_: *mut leanh::LeanObject,
    mut v_t_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0_spec__0(v_init_1526_, v_t_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0___boxed(
    mut v_init_1529_: *mut leanh::LeanObject,
    mut v_t_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2__spec__0(v_init_1529_, v_t_1530_);
    leanh::lean_dec(v_t_1530_);
    return v_res_1531_;
}
pub unsafe fn l_Lean_Meta_getFunInductName(
    mut v_declName_1538_: *mut leanh::LeanObject,
    mut v_unfolding_1539_: u8,
) -> *mut leanh::LeanObject {
    if v_unfolding_1539_ == 0 {
        let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1540_ = l_Lean_Meta_getFunInductName___closed__1;
        v___x_1541_ = l_Lean_Name_append(v_declName_1538_, v___x_1540_);
        return v___x_1541_;
    } else {
        let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1542_ = l_Lean_Meta_getFunInductName___closed__3;
        v___x_1543_ = l_Lean_Name_append(v_declName_1538_, v___x_1542_);
        return v___x_1543_;
    }
}
pub unsafe fn l_Lean_Meta_getFunInductName___boxed(
    mut v_declName_1544_: *mut leanh::LeanObject,
    mut v_unfolding_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unfolding_boxed_1546_: u8 = 0;
    let mut v_res_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unfolding_boxed_1546_ = (leanh::lean_unbox(v_unfolding_1545_) as u8);
    v_res_1547_ = l_Lean_Meta_getFunInductName(v_declName_1544_, v_unfolding_boxed_1546_);
    return v_res_1547_;
}
pub unsafe fn l_Lean_Meta_getFunCasesName(
    mut v_declName_1554_: *mut leanh::LeanObject,
    mut v_unfolding_1555_: u8,
) -> *mut leanh::LeanObject {
    if v_unfolding_1555_ == 0 {
        let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1556_ = l_Lean_Meta_getFunCasesName___closed__1;
        v___x_1557_ = l_Lean_Name_append(v_declName_1554_, v___x_1556_);
        return v___x_1557_;
    } else {
        let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1558_ = l_Lean_Meta_getFunCasesName___closed__3;
        v___x_1559_ = l_Lean_Name_append(v_declName_1554_, v___x_1558_);
        return v___x_1559_;
    }
}
pub unsafe fn l_Lean_Meta_getFunCasesName___boxed(
    mut v_declName_1560_: *mut leanh::LeanObject,
    mut v_unfolding_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unfolding_boxed_1562_: u8 = 0;
    let mut v_res_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unfolding_boxed_1562_ = (leanh::lean_unbox(v_unfolding_1561_) as u8);
    v_res_1563_ = l_Lean_Meta_getFunCasesName(v_declName_1560_, v_unfolding_boxed_1562_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_Meta_getMutualInductName(
    mut v_declName_1570_: *mut leanh::LeanObject,
    mut v_unfolding_1571_: u8,
) -> *mut leanh::LeanObject {
    if v_unfolding_1571_ == 0 {
        let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1572_ = l_Lean_Meta_getMutualInductName___closed__1;
        v___x_1573_ = l_Lean_Name_append(v_declName_1570_, v___x_1572_);
        return v___x_1573_;
    } else {
        let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1574_ = l_Lean_Meta_getMutualInductName___closed__3;
        v___x_1575_ = l_Lean_Name_append(v_declName_1570_, v___x_1574_);
        return v___x_1575_;
    }
}
pub unsafe fn l_Lean_Meta_getMutualInductName___boxed(
    mut v_declName_1576_: *mut leanh::LeanObject,
    mut v_unfolding_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unfolding_boxed_1578_: u8 = 0;
    let mut v_res_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unfolding_boxed_1578_ = (leanh::lean_unbox(v_unfolding_1577_) as u8);
    v_res_1579_ = l_Lean_Meta_getMutualInductName(v_declName_1576_, v_unfolding_boxed_1578_);
    return v_res_1579_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1580_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1581_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1582_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1582_, 0, v___x_1581_);
    return v___x_1582_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1584_ = leanh::lean_unsigned_to_nat(0);
    v___x_1585_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1585_, 0, v___x_1584_);
    leanh::lean_ctor_set(v___x_1585_, 1, v___x_1584_);
    leanh::lean_ctor_set(v___x_1585_, 2, v___x_1584_);
    leanh::lean_ctor_set(v___x_1585_, 3, v___x_1584_);
    leanh::lean_ctor_set(v___x_1585_, 4, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 5, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 6, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 7, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 8, v___x_1583_);
    leanh::lean_ctor_set(v___x_1585_, 9, v___x_1583_);
    return v___x_1585_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1586_ = leanh::lean_unsigned_to_nat(32);
    v___x_1587_ = lean_mk_empty_array_with_capacity(v___x_1586_);
    v___x_1588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1588_, 0, v___x_1587_);
    return v___x_1588_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1589_: usize = 0;
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1589_ = 5usize;
    v___x_1590_ = leanh::lean_unsigned_to_nat(0);
    v___x_1591_ = leanh::lean_unsigned_to_nat(32);
    v___x_1592_ = lean_mk_empty_array_with_capacity(v___x_1591_);
    v___x_1593_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1594_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    leanh::lean_ctor_set(v___x_1594_, 1, v___x_1592_);
    leanh::lean_ctor_set(v___x_1594_, 2, v___x_1590_);
    leanh::lean_ctor_set(v___x_1594_, 3, v___x_1590_);
    leanh::lean_ctor_set_usize(v___x_1594_, 4, v___x_1589_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = leanh::lean_box(1);
    v___x_1596_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1598_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1598_, 0, v___x_1597_);
    leanh::lean_ctor_set(v___x_1598_, 1, v___x_1596_);
    leanh::lean_ctor_set(v___x_1598_, 2, v___x_1595_);
    return v___x_1598_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1601_ = l_Lean_stringToMessageData(v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1604_ = l_Lean_stringToMessageData(v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1607_ = l_Lean_stringToMessageData(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1609_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1612_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1613_ = l_Lean_stringToMessageData(v___x_1612_);
    return v___x_1613_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1616_ = l_Lean_stringToMessageData(v___x_1615_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1618_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1619_ = l_Lean_stringToMessageData(v___x_1618_);
    return v___x_1619_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1620_: *mut leanh::LeanObject,
    mut v_declHint_1621_: *mut leanh::LeanObject,
    mut v___y_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: u8 = 0;
    let mut v_isExporting_1627_: u8 = 0;
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1681_: u8 = 0;
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1624_ = lean_st_ref_get(v___y_1622_);
                v_env_1625_ = leanh::lean_ctor_get(v___x_1624_, 0);
                leanh::lean_inc_ref(v_env_1625_);
                leanh::lean_dec(v___x_1624_);
                v___x_1626_ = l_Lean_Name_isAnonymous(v_declHint_1621_);
                if v___x_1626_ == 0 {
                    v_isExporting_1627_ = leanh::lean_ctor_get_uint8(
                        v_env_1625_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1627_ == 0 {
                        leanh::lean_dec_ref(v_env_1625_);
                        leanh::lean_dec(v_declHint_1621_);
                        v___x_1628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1628_, 0, v_msg_1620_);
                        return v___x_1628_;
                    } else {
                        leanh::lean_inc_ref(v_env_1625_);
                        v___x_1629_ = l_Lean_Environment_setExporting(v_env_1625_, v___x_1626_);
                        leanh::lean_inc(v_declHint_1621_);
                        leanh::lean_inc_ref(v___x_1629_);
                        v___x_1630_ = l_Lean_Environment_contains(
                            v___x_1629_,
                            v_declHint_1621_,
                            v_isExporting_1627_,
                        );
                        if v___x_1630_ == 0 {
                            leanh::lean_dec_ref(v___x_1629_);
                            leanh::lean_dec_ref(v_env_1625_);
                            leanh::lean_dec(v_declHint_1621_);
                            v___x_1631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1631_, 0, v_msg_1620_);
                            return v___x_1631_;
                        } else {
                            v___x_1632_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1633_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1634_ = l_Lean_Options_empty;
                            v___x_1635_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1635_, 0, v___x_1629_);
                            leanh::lean_ctor_set(v___x_1635_, 1, v___x_1632_);
                            leanh::lean_ctor_set(v___x_1635_, 2, v___x_1633_);
                            leanh::lean_ctor_set(v___x_1635_, 3, v___x_1634_);
                            leanh::lean_inc(v_declHint_1621_);
                            v___x_1636_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1621_, v___x_1626_);
                            v_c_1637_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1637_, 0, v___x_1635_);
                            leanh::lean_ctor_set(v_c_1637_, 1, v___x_1636_);
                            v___x_1638_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1625_,
                                v_declHint_1621_,
                            );
                            if leanh::lean_obj_tag(v___x_1638_) == 0 {
                                leanh::lean_dec_ref(v_env_1625_);
                                leanh::lean_dec(v_declHint_1621_);
                                v___x_1639_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1640_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                                leanh::lean_ctor_set(v___x_1640_, 1, v_c_1637_);
                                v___x_1641_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1642_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1642_, 0, v___x_1640_);
                                leanh::lean_ctor_set(v___x_1642_, 1, v___x_1641_);
                                v___x_1643_ = l_Lean_MessageData_note(v___x_1642_);
                                v___x_1644_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1644_, 0, v_msg_1620_);
                                leanh::lean_ctor_set(v___x_1644_, 1, v___x_1643_);
                                v___x_1645_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1645_, 0, v___x_1644_);
                                return v___x_1645_;
                            } else {
                                v_val_1646_ = leanh::lean_ctor_get(v___x_1638_, 0);
                                v_isSharedCheck_1681_ =
                                    (!leanh::lean_is_exclusive(v___x_1638_)) as u8;
                                if v_isSharedCheck_1681_ == 0 {
                                    v___x_1648_ = v___x_1638_;
                                    v_isShared_1649_ = v_isSharedCheck_1681_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1646_);
                                    leanh::lean_dec(v___x_1638_);
                                    v___x_1648_ = leanh::lean_box(0);
                                    v_isShared_1649_ = v_isSharedCheck_1681_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1625_);
                    leanh::lean_dec(v_declHint_1621_);
                    v___x_1682_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1682_, 0, v_msg_1620_);
                    return v___x_1682_;
                }
            }
            1 => {
                v___x_1650_ = leanh::lean_box(0);
                v___x_1651_ = l_Lean_Environment_header(v_env_1625_);
                leanh::lean_dec_ref(v_env_1625_);
                v___x_1652_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1651_);
                v_mod_1653_ = lean_array_get(v___x_1650_, v___x_1652_, v_val_1646_);
                leanh::lean_dec(v_val_1646_);
                leanh::lean_dec_ref(v___x_1652_);
                v___x_1654_ = l_Lean_isPrivateName(v_declHint_1621_);
                leanh::lean_dec(v_declHint_1621_);
                if v___x_1654_ == 0 {
                    v___x_1655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1656_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1656_, 0, v___x_1655_);
                    leanh::lean_ctor_set(v___x_1656_, 1, v_c_1637_);
                    v___x_1657_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1658_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1658_, 0, v___x_1656_);
                    leanh::lean_ctor_set(v___x_1658_, 1, v___x_1657_);
                    v___x_1659_ = l_Lean_MessageData_ofName(v_mod_1653_);
                    v___x_1660_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1660_, 0, v___x_1658_);
                    leanh::lean_ctor_set(v___x_1660_, 1, v___x_1659_);
                    v___x_1661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1662_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1662_, 0, v___x_1660_);
                    leanh::lean_ctor_set(v___x_1662_, 1, v___x_1661_);
                    v___x_1663_ = l_Lean_MessageData_note(v___x_1662_);
                    v___x_1664_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1664_, 0, v_msg_1620_);
                    leanh::lean_ctor_set(v___x_1664_, 1, v___x_1663_);
                    if v_isShared_1649_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1648_, 0);
                        leanh::lean_ctor_set(v___x_1648_, 0, v___x_1664_);
                        v___x_1666_ = v___x_1648_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
                        v___x_1666_ = v_reuseFailAlloc_1667_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1668_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1669_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1669_, 0, v___x_1668_);
                    leanh::lean_ctor_set(v___x_1669_, 1, v_c_1637_);
                    v___x_1670_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1671_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1671_, 0, v___x_1669_);
                    leanh::lean_ctor_set(v___x_1671_, 1, v___x_1670_);
                    v___x_1672_ = l_Lean_MessageData_ofName(v_mod_1653_);
                    v___x_1673_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1673_, 0, v___x_1671_);
                    leanh::lean_ctor_set(v___x_1673_, 1, v___x_1672_);
                    v___x_1674_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1675_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1675_, 0, v___x_1673_);
                    leanh::lean_ctor_set(v___x_1675_, 1, v___x_1674_);
                    v___x_1676_ = l_Lean_MessageData_note(v___x_1675_);
                    v___x_1677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1677_, 0, v_msg_1620_);
                    leanh::lean_ctor_set(v___x_1677_, 1, v___x_1676_);
                    if v_isShared_1649_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1648_, 0);
                        leanh::lean_ctor_set(v___x_1648_, 0, v___x_1677_);
                        v___x_1679_ = v___x_1648_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1680_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1677_);
                        v___x_1679_ = v_reuseFailAlloc_1680_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1666_;
            }
            3 => {
                return v___x_1679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1683_: *mut leanh::LeanObject,
    mut v_declHint_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1687_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1683_, v_declHint_1684_, v___y_1685_);
    leanh::lean_dec(v___y_1685_);
    return v_res_1687_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1688_: *mut leanh::LeanObject,
    mut v_declHint_1689_: *mut leanh::LeanObject,
    mut v___y_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1697_: u8 = 0;
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1693_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1688_, v_declHint_1689_, v___y_1691_);
                v_a_1694_ = leanh::lean_ctor_get(v___x_1693_, 0);
                v_isSharedCheck_1703_ = (!leanh::lean_is_exclusive(v___x_1693_)) as u8;
                if v_isSharedCheck_1703_ == 0 {
                    v___x_1696_ = v___x_1693_;
                    v_isShared_1697_ = v_isSharedCheck_1703_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1694_);
                    leanh::lean_dec(v___x_1693_);
                    v___x_1696_ = leanh::lean_box(0);
                    v_isShared_1697_ = v_isSharedCheck_1703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1698_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1699_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1699_, 0, v___x_1698_);
                leanh::lean_ctor_set(v___x_1699_, 1, v_a_1694_);
                if v_isShared_1697_ == 0 {
                    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1699_);
                    v___x_1701_ = v___x_1696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1702_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
                    v___x_1701_ = v_reuseFailAlloc_1702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1704_: *mut leanh::LeanObject,
    mut v_declHint_1705_: *mut leanh::LeanObject,
    mut v___y_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1704_, v_declHint_1705_, v___y_1706_, v___y_1707_);
    leanh::lean_dec(v___y_1707_);
    leanh::lean_dec_ref(v___y_1706_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1710_: *mut leanh::LeanObject,
    mut v___y_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = lean_st_ref_get(v___y_1712_);
    v_env_1715_ = leanh::lean_ctor_get(v___x_1714_, 0);
    leanh::lean_inc_ref(v_env_1715_);
    leanh::lean_dec(v___x_1714_);
    v_options_1716_ = leanh::lean_ctor_get(v___y_1711_, 2);
    v___x_1717_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
    v___x_1718_ = leanh::lean_unsigned_to_nat(32);
    v___x_1719_ = lean_mk_empty_array_with_capacity(v___x_1718_);
    leanh::lean_dec_ref(v___x_1719_);
    v___x_1720_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
    leanh::lean_inc_ref(v_options_1716_);
    v___x_1721_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1721_, 0, v_env_1715_);
    leanh::lean_ctor_set(v___x_1721_, 1, v___x_1717_);
    leanh::lean_ctor_set(v___x_1721_, 2, v___x_1720_);
    leanh::lean_ctor_set(v___x_1721_, 3, v_options_1716_);
    v___x_1722_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1722_, 0, v___x_1721_);
    leanh::lean_ctor_set(v___x_1722_, 1, v_msgData_1710_);
    v___x_1723_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1723_, 0, v___x_1722_);
    return v___x_1723_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1728_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1724_, v___y_1725_, v___y_1726_);
    leanh::lean_dec(v___y_1726_);
    leanh::lean_dec_ref(v___y_1725_);
    return v_res_1728_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1733_ = leanh::lean_ctor_get(v___y_1730_, 5);
                v___x_1734_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1729_, v___y_1730_, v___y_1731_);
                v_a_1735_ = leanh::lean_ctor_get(v___x_1734_, 0);
                v_isSharedCheck_1743_ = (!leanh::lean_is_exclusive(v___x_1734_)) as u8;
                if v_isSharedCheck_1743_ == 0 {
                    v___x_1737_ = v___x_1734_;
                    v_isShared_1738_ = v_isSharedCheck_1743_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1735_);
                    leanh::lean_dec(v___x_1734_);
                    v___x_1737_ = leanh::lean_box(0);
                    v_isShared_1738_ = v_isSharedCheck_1743_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1733_);
                v___x_1739_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1739_, 0, v_ref_1733_);
                leanh::lean_ctor_set(v___x_1739_, 1, v_a_1735_);
                if v_isShared_1738_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1737_, 1);
                    leanh::lean_ctor_set(v___x_1737_, 0, v___x_1739_);
                    v___x_1741_ = v___x_1737_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1744_, v___y_1745_, v___y_1746_);
    leanh::lean_dec(v___y_1746_);
    leanh::lean_dec_ref(v___y_1745_);
    return v_res_1748_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1749_: *mut leanh::LeanObject,
    mut v_msg_1750_: *mut leanh::LeanObject,
    mut v___y_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1766_: u8 = 0;
    let mut v_cancelTk_x3f_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1768_: u8 = 0;
    let mut v_inheritedTraceOptions_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1754_ = leanh::lean_ctor_get(v___y_1751_, 0);
    v_fileMap_1755_ = leanh::lean_ctor_get(v___y_1751_, 1);
    v_options_1756_ = leanh::lean_ctor_get(v___y_1751_, 2);
    v_currRecDepth_1757_ = leanh::lean_ctor_get(v___y_1751_, 3);
    v_maxRecDepth_1758_ = leanh::lean_ctor_get(v___y_1751_, 4);
    v_ref_1759_ = leanh::lean_ctor_get(v___y_1751_, 5);
    v_currNamespace_1760_ = leanh::lean_ctor_get(v___y_1751_, 6);
    v_openDecls_1761_ = leanh::lean_ctor_get(v___y_1751_, 7);
    v_initHeartbeats_1762_ = leanh::lean_ctor_get(v___y_1751_, 8);
    v_maxHeartbeats_1763_ = leanh::lean_ctor_get(v___y_1751_, 9);
    v_quotContext_1764_ = leanh::lean_ctor_get(v___y_1751_, 10);
    v_currMacroScope_1765_ = leanh::lean_ctor_get(v___y_1751_, 11);
    v_diag_1766_ = leanh::lean_ctor_get_uint8(
        v___y_1751_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1767_ = leanh::lean_ctor_get(v___y_1751_, 12);
    v_suppressElabErrors_1768_ = leanh::lean_ctor_get_uint8(
        v___y_1751_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1769_ = leanh::lean_ctor_get(v___y_1751_, 13);
    v_ref_1770_ = l_Lean_replaceRef(v_ref_1749_, v_ref_1759_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1769_);
    leanh::lean_inc(v_cancelTk_x3f_1767_);
    leanh::lean_inc(v_currMacroScope_1765_);
    leanh::lean_inc(v_quotContext_1764_);
    leanh::lean_inc(v_maxHeartbeats_1763_);
    leanh::lean_inc(v_initHeartbeats_1762_);
    leanh::lean_inc(v_openDecls_1761_);
    leanh::lean_inc(v_currNamespace_1760_);
    leanh::lean_inc(v_maxRecDepth_1758_);
    leanh::lean_inc(v_currRecDepth_1757_);
    leanh::lean_inc_ref(v_options_1756_);
    leanh::lean_inc_ref(v_fileMap_1755_);
    leanh::lean_inc_ref(v_fileName_1754_);
    v___x_1771_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1771_, 0, v_fileName_1754_);
    leanh::lean_ctor_set(v___x_1771_, 1, v_fileMap_1755_);
    leanh::lean_ctor_set(v___x_1771_, 2, v_options_1756_);
    leanh::lean_ctor_set(v___x_1771_, 3, v_currRecDepth_1757_);
    leanh::lean_ctor_set(v___x_1771_, 4, v_maxRecDepth_1758_);
    leanh::lean_ctor_set(v___x_1771_, 5, v_ref_1770_);
    leanh::lean_ctor_set(v___x_1771_, 6, v_currNamespace_1760_);
    leanh::lean_ctor_set(v___x_1771_, 7, v_openDecls_1761_);
    leanh::lean_ctor_set(v___x_1771_, 8, v_initHeartbeats_1762_);
    leanh::lean_ctor_set(v___x_1771_, 9, v_maxHeartbeats_1763_);
    leanh::lean_ctor_set(v___x_1771_, 10, v_quotContext_1764_);
    leanh::lean_ctor_set(v___x_1771_, 11, v_currMacroScope_1765_);
    leanh::lean_ctor_set(v___x_1771_, 12, v_cancelTk_x3f_1767_);
    leanh::lean_ctor_set(v___x_1771_, 13, v_inheritedTraceOptions_1769_);
    leanh::lean_ctor_set_uint8(
        v___x_1771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1766_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1771_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1768_,
    );
    v___x_1772_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1750_, v___x_1771_, v___y_1752_);
    leanh::lean_dec_ref_known(v___x_1771_, 14);
    return v___x_1772_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1773_: *mut leanh::LeanObject,
    mut v_msg_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
    mut v___y_1776_: *mut leanh::LeanObject,
    mut v___y_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1773_, v_msg_1774_, v___y_1775_, v___y_1776_);
    leanh::lean_dec(v___y_1776_);
    leanh::lean_dec_ref(v___y_1775_);
    leanh::lean_dec(v_ref_1773_);
    return v_res_1778_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1779_: *mut leanh::LeanObject,
    mut v_msg_1780_: *mut leanh::LeanObject,
    mut v_declHint_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1785_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1780_, v_declHint_1781_, v___y_1782_, v___y_1783_);
    v_a_1786_ = leanh::lean_ctor_get(v___x_1785_, 0);
    leanh::lean_inc(v_a_1786_);
    leanh::lean_dec_ref(v___x_1785_);
    v___x_1787_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1779_, v_a_1786_, v___y_1782_, v___y_1783_);
    return v___x_1787_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1788_: *mut leanh::LeanObject,
    mut v_msg_1789_: *mut leanh::LeanObject,
    mut v_declHint_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1788_, v_msg_1789_, v_declHint_1790_, v___y_1791_, v___y_1792_);
    leanh::lean_dec(v___y_1792_);
    leanh::lean_dec_ref(v___y_1791_);
    leanh::lean_dec(v_ref_1788_);
    return v_res_1794_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1796_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1797_ = l_Lean_stringToMessageData(v___x_1796_);
    return v___x_1797_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1799_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1800_ = l_Lean_stringToMessageData(v___x_1799_);
    return v___x_1800_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1801_: *mut leanh::LeanObject,
    mut v_constName_1802_: *mut leanh::LeanObject,
    mut v___y_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1807_ = 0;
    leanh::lean_inc(v_constName_1802_);
    v___x_1808_ = l_Lean_MessageData_ofConstName(v_constName_1802_, v___x_1807_);
    v___x_1809_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1809_, 0, v___x_1806_);
    leanh::lean_ctor_set(v___x_1809_, 1, v___x_1808_);
    v___x_1810_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1811_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1811_, 0, v___x_1809_);
    leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
    v___x_1812_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1801_, v___x_1811_, v_constName_1802_, v___y_1803_, v___y_1804_);
    return v___x_1812_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1813_: *mut leanh::LeanObject,
    mut v_constName_1814_: *mut leanh::LeanObject,
    mut v___y_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1818_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1813_, v_constName_1814_, v___y_1815_, v___y_1816_);
    leanh::lean_dec(v___y_1816_);
    leanh::lean_dec_ref(v___y_1815_);
    leanh::lean_dec(v_ref_1813_);
    return v_res_1818_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(
    mut v_constName_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1823_ = leanh::lean_ctor_get(v___y_1820_, 5);
    v___x_1824_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1823_, v_constName_1819_, v___y_1820_, v___y_1821_);
    return v___x_1824_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_1825_, v___y_1826_, v___y_1827_);
    leanh::lean_dec(v___y_1827_);
    leanh::lean_dec_ref(v___y_1826_);
    return v_res_1829_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(
    mut v_constName_1830_: *mut leanh::LeanObject,
    mut v___y_1831_: *mut leanh::LeanObject,
    mut v___y_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1842_: u8 = 0;
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1834_ = lean_st_ref_get(v___y_1832_);
                v_env_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                leanh::lean_inc_ref(v_env_1835_);
                leanh::lean_dec(v___x_1834_);
                v___x_1836_ = 0;
                leanh::lean_inc(v_constName_1830_);
                v___x_1837_ =
                    l_Lean_Environment_find_x3f(v_env_1835_, v_constName_1830_, v___x_1836_);
                if leanh::lean_obj_tag(v___x_1837_) == 0 {
                    v___x_1838_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_1830_, v___y_1831_, v___y_1832_);
                    return v___x_1838_;
                } else {
                    leanh::lean_dec(v_constName_1830_);
                    v_val_1839_ = leanh::lean_ctor_get(v___x_1837_, 0);
                    v_isSharedCheck_1846_ = (!leanh::lean_is_exclusive(v___x_1837_)) as u8;
                    if v_isSharedCheck_1846_ == 0 {
                        v___x_1841_ = v___x_1837_;
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1839_);
                        leanh::lean_dec(v___x_1837_);
                        v___x_1841_ = leanh::lean_box(0);
                        v_isShared_1842_ = v_isSharedCheck_1846_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1842_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1841_, 0);
                    v___x_1844_ = v___x_1841_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1845_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_val_1839_);
                    v___x_1844_ = v_reuseFailAlloc_1845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0___boxed(
    mut v_constName_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
    mut v___y_1850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1851_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(
        v_constName_1847_,
        v___y_1848_,
        v___y_1849_,
    );
    leanh::lean_dec(v___y_1849_);
    leanh::lean_dec_ref(v___y_1848_);
    return v_res_1851_;
}
pub unsafe fn l_Lean_Meta_getFunInduct_x3f(
    mut v_unfolding_1852_: u8,
    mut v_cases_1853_: u8,
    mut v_declName_1854_: *mut leanh::LeanObject,
    mut v_a_1855_: *mut leanh::LeanObject,
    mut v_a_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1860_: u8 = 0;
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1868_: u8 = 0;
    let mut v___y_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1880_: u8 = 0;
    let mut v_a_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1890_: u8 = 0;
    let mut v_a_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1894_: u8 = 0;
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_1854_);
                v___x_1864_ = l_Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0(
                    v_declName_1854_,
                    v_a_1855_,
                    v_a_1856_,
                );
                if leanh::lean_obj_tag(v___x_1864_) == 0 {
                    v_a_1865_ = leanh::lean_ctor_get(v___x_1864_, 0);
                    v_isSharedCheck_1890_ = (!leanh::lean_is_exclusive(v___x_1864_)) as u8;
                    if v_isSharedCheck_1890_ == 0 {
                        v___x_1867_ = v___x_1864_;
                        v_isShared_1868_ = v_isSharedCheck_1890_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1865_);
                        leanh::lean_dec(v___x_1864_);
                        v___x_1867_ = leanh::lean_box(0);
                        v_isShared_1868_ = v_isSharedCheck_1890_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_1854_);
                    v_a_1891_ = leanh::lean_ctor_get(v___x_1864_, 0);
                    v_isSharedCheck_1898_ = (!leanh::lean_is_exclusive(v___x_1864_)) as u8;
                    if v_isSharedCheck_1898_ == 0 {
                        v___x_1893_ = v___x_1864_;
                        v_isShared_1894_ = v_isSharedCheck_1898_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1891_);
                        leanh::lean_dec(v___x_1864_);
                        v___x_1893_ = leanh::lean_box(0);
                        v_isShared_1894_ = v_isSharedCheck_1898_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1860_ == 0 {
                    leanh::lean_dec_ref(v___y_1859_);
                    v___x_1861_ = leanh::lean_box(0);
                    v___x_1862_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1862_, 0, v___x_1861_);
                    return v___x_1862_;
                } else {
                    v___x_1863_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1863_, 0, v___y_1859_);
                    return v___x_1863_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_1865_) == 1 {
                    leanh::lean_dec_ref_known(v_a_1865_, 1);
                    leanh::lean_del_object(v___x_1867_);
                    if v_cases_1853_ == 0 {
                        v___x_1884_ =
                            l_Lean_Meta_getFunInductName(v_declName_1854_, v_unfolding_1852_);
                        v___y_1870_ = v___x_1884_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1885_ =
                            l_Lean_Meta_getFunCasesName(v_declName_1854_, v_unfolding_1852_);
                        v___y_1870_ = v___x_1885_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1865_);
                    leanh::lean_dec(v_declName_1854_);
                    v___x_1886_ = leanh::lean_box(0);
                    if v_isShared_1868_ == 0 {
                        leanh::lean_ctor_set(v___x_1867_, 0, v___x_1886_);
                        v___x_1888_ = v___x_1867_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1889_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1886_);
                        v___x_1888_ = v_reuseFailAlloc_1889_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1871_ =
                    l_Lean_realizeGlobalConstNoOverloadCore(v___y_1870_, v_a_1855_, v_a_1856_);
                if leanh::lean_obj_tag(v___x_1871_) == 0 {
                    v_a_1872_ = leanh::lean_ctor_get(v___x_1871_, 0);
                    v_isSharedCheck_1880_ = (!leanh::lean_is_exclusive(v___x_1871_)) as u8;
                    if v_isSharedCheck_1880_ == 0 {
                        v___x_1874_ = v___x_1871_;
                        v_isShared_1875_ = v_isSharedCheck_1880_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1872_);
                        leanh::lean_dec(v___x_1871_);
                        v___x_1874_ = leanh::lean_box(0);
                        v_isShared_1875_ = v_isSharedCheck_1880_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_1881_ = leanh::lean_ctor_get(v___x_1871_, 0);
                    leanh::lean_inc(v_a_1881_);
                    leanh::lean_dec_ref_known(v___x_1871_, 1);
                    v___x_1882_ = l_Lean_Exception_isInterrupt(v_a_1881_);
                    if v___x_1882_ == 0 {
                        leanh::lean_inc(v_a_1881_);
                        v___x_1883_ = l_Lean_Exception_isRuntime(v_a_1881_);
                        v___y_1859_ = v_a_1881_;
                        v___y_1860_ = v___x_1883_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1859_ = v_a_1881_;
                        v___y_1860_ = v___x_1882_;
                        state = 1;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1876_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1876_, 0, v_a_1872_);
                if v_isShared_1875_ == 0 {
                    leanh::lean_ctor_set(v___x_1874_, 0, v___x_1876_);
                    v___x_1878_ = v___x_1874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
                    v___x_1878_ = v_reuseFailAlloc_1879_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1878_;
            }
            6 => {
                return v___x_1888_;
            }
            7 => {
                if v_isShared_1894_ == 0 {
                    v___x_1896_ = v___x_1893_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
                    v___x_1896_ = v_reuseFailAlloc_1897_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFunInduct_x3f___boxed(
    mut v_unfolding_1899_: *mut leanh::LeanObject,
    mut v_cases_1900_: *mut leanh::LeanObject,
    mut v_declName_1901_: *mut leanh::LeanObject,
    mut v_a_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_unfolding_boxed_1905_: u8 = 0;
    let mut v_cases_boxed_1906_: u8 = 0;
    let mut v_res_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_unfolding_boxed_1905_ = (leanh::lean_unbox(v_unfolding_1899_) as u8);
    v_cases_boxed_1906_ = (leanh::lean_unbox(v_cases_1900_) as u8);
    v_res_1907_ = l_Lean_Meta_getFunInduct_x3f(
        v_unfolding_boxed_1905_,
        v_cases_boxed_1906_,
        v_declName_1901_,
        v_a_1902_,
        v_a_1903_,
    );
    leanh::lean_dec(v_a_1903_);
    leanh::lean_dec_ref(v_a_1902_);
    return v_res_1907_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(
    mut v_00_u03b1_1908_: *mut leanh::LeanObject,
    mut v_constName_1909_: *mut leanh::LeanObject,
    mut v___y_1910_: *mut leanh::LeanObject,
    mut v___y_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1913_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___redArg(v_constName_1909_, v___y_1910_, v___y_1911_);
    return v___x_1913_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_1914_: *mut leanh::LeanObject,
    mut v_constName_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0(v_00_u03b1_1914_, v_constName_1915_, v___y_1916_, v___y_1917_);
    leanh::lean_dec(v___y_1917_);
    leanh::lean_dec_ref(v___y_1916_);
    return v_res_1919_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1920_: *mut leanh::LeanObject,
    mut v_ref_1921_: *mut leanh::LeanObject,
    mut v_constName_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___redArg(v_ref_1921_, v_constName_1922_, v___y_1923_, v___y_1924_);
    return v___x_1926_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1927_: *mut leanh::LeanObject,
    mut v_ref_1928_: *mut leanh::LeanObject,
    mut v_constName_1929_: *mut leanh::LeanObject,
    mut v___y_1930_: *mut leanh::LeanObject,
    mut v___y_1931_: *mut leanh::LeanObject,
    mut v___y_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1(v_00_u03b1_1927_, v_ref_1928_, v_constName_1929_, v___y_1930_, v___y_1931_);
    leanh::lean_dec(v___y_1931_);
    leanh::lean_dec_ref(v___y_1930_);
    leanh::lean_dec(v_ref_1928_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1934_: *mut leanh::LeanObject,
    mut v_ref_1935_: *mut leanh::LeanObject,
    mut v_msg_1936_: *mut leanh::LeanObject,
    mut v_declHint_1937_: *mut leanh::LeanObject,
    mut v___y_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1935_, v_msg_1936_, v_declHint_1937_, v___y_1938_, v___y_1939_);
    return v___x_1941_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1942_: *mut leanh::LeanObject,
    mut v_ref_1943_: *mut leanh::LeanObject,
    mut v_msg_1944_: *mut leanh::LeanObject,
    mut v_declHint_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1942_, v_ref_1943_, v_msg_1944_, v_declHint_1945_, v___y_1946_, v___y_1947_);
    leanh::lean_dec(v___y_1947_);
    leanh::lean_dec_ref(v___y_1946_);
    leanh::lean_dec(v_ref_1943_);
    return v_res_1949_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1950_: *mut leanh::LeanObject,
    mut v_declHint_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1955_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1950_, v_declHint_1951_, v___y_1953_);
    return v___x_1955_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1956_: *mut leanh::LeanObject,
    mut v_declHint_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1956_, v_declHint_1957_, v___y_1958_, v___y_1959_);
    leanh::lean_dec(v___y_1959_);
    leanh::lean_dec_ref(v___y_1958_);
    return v_res_1961_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1962_: *mut leanh::LeanObject,
    mut v_ref_1963_: *mut leanh::LeanObject,
    mut v_msg_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1968_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1963_, v_msg_1964_, v___y_1965_, v___y_1966_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_1969_: *mut leanh::LeanObject,
    mut v_ref_1970_: *mut leanh::LeanObject,
    mut v_msg_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1969_, v_ref_1970_, v_msg_1971_, v___y_1972_, v___y_1973_);
    leanh::lean_dec(v___y_1973_);
    leanh::lean_dec_ref(v___y_1972_);
    leanh::lean_dec(v_ref_1970_);
    return v_res_1975_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_1976_: *mut leanh::LeanObject,
    mut v_msg_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1981_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1977_, v___y_1978_, v___y_1979_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_1982_: *mut leanh::LeanObject,
    mut v_msg_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
    mut v___y_1985_: *mut leanh::LeanObject,
    mut v___y_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_getFunInduct_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1982_, v_msg_1983_, v___y_1984_, v___y_1985_);
    leanh::lean_dec(v___y_1985_);
    leanh::lean_dec_ref(v___y_1984_);
    return v_res_1987_;
}
pub unsafe fn l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(
    mut v_msg_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432__overap_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1993_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___closed__0;
    v___x_432__overap_1994_ = lean_panic_fn_borrowed(v___f_1993_, v_msg_1989_);
    leanh::lean_inc(v___y_1991_);
    leanh::lean_inc_ref(v___y_1990_);
    v___x_1995_ = leanh::lean_apply_3(
        v___x_432__overap_1994_,
        v___y_1990_,
        v___y_1991_,
        leanh::lean_box(0),
    );
    return v___x_1995_;
}
pub unsafe fn l_panic___at___00Lean_Meta_setFunIndInfo_spec__0___boxed(
    mut v_msg_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2000_ =
        l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(v_msg_1996_, v___y_1997_, v___y_1998_);
    leanh::lean_dec(v___y_1998_);
    leanh::lean_dec_ref(v___y_1997_);
    return v_res_2000_;
}
pub unsafe fn _init_l_Lean_Meta_setFunIndInfo___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2001_;
}
pub unsafe fn _init_l_Lean_Meta_setFunIndInfo___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2002_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__0_once),
        _init_l_Lean_Meta_setFunIndInfo___closed__0,
    );
    v___x_2003_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2003_, 0, v___x_2002_);
    return v___x_2003_;
}
pub unsafe fn _init_l_Lean_Meta_setFunIndInfo___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2004_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__1_once),
        _init_l_Lean_Meta_setFunIndInfo___closed__1,
    );
    v___x_2005_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2005_, 0, v___x_2004_);
    leanh::lean_ctor_set(v___x_2005_, 1, v___x_2004_);
    return v___x_2005_;
}
pub unsafe fn _init_l_Lean_Meta_setFunIndInfo___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = l_Lean_Meta_setFunIndInfo___closed__5;
    v___x_2010_ = leanh::lean_unsigned_to_nat(2);
    v___x_2011_ = leanh::lean_unsigned_to_nat(79);
    v___x_2012_ = l_Lean_Meta_setFunIndInfo___closed__4;
    v___x_2013_ = l_Lean_Meta_setFunIndInfo___closed__3;
    v___x_2014_ = l_mkPanicMessageWithDecl(
        v___x_2013_,
        v___x_2012_,
        v___x_2011_,
        v___x_2010_,
        v___x_2009_,
    );
    return v___x_2014_;
}
pub unsafe fn l_Lean_Meta_setFunIndInfo(
    mut v_funIndInfo_2015_: *mut leanh::LeanObject,
    mut v_a_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_funIndName_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: u8 = 0;
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2036_: u8 = 0;
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2045_: u8 = 0;
    let mut v_unused_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2019_ = lean_st_ref_get(v_a_2017_);
                v_env_2020_ = leanh::lean_ctor_get(v___x_2019_, 0);
                leanh::lean_inc_ref(v_env_2020_);
                leanh::lean_dec(v___x_2019_);
                v_funIndName_2021_ = leanh::lean_ctor_get(v_funIndInfo_2015_, 1);
                leanh::lean_inc_n(v_funIndName_2021_, 2);
                v___x_2022_ = l_Lean_Meta_instInhabitedFunIndInfo_default;
                v___x_2023_ = l_Lean_Meta_funIndInfoExt;
                v___x_2024_ = l_Lean_MapDeclarationExtension_contains___redArg(
                    v___x_2022_,
                    v___x_2023_,
                    v_env_2020_,
                    v_funIndName_2021_,
                );
                if v___x_2024_ == 0 {
                    v___x_2025_ = lean_st_ref_take(v_a_2017_);
                    v_env_2026_ = leanh::lean_ctor_get(v___x_2025_, 0);
                    v_nextMacroScope_2027_ = leanh::lean_ctor_get(v___x_2025_, 1);
                    v_ngen_2028_ = leanh::lean_ctor_get(v___x_2025_, 2);
                    v_auxDeclNGen_2029_ = leanh::lean_ctor_get(v___x_2025_, 3);
                    v_traceState_2030_ = leanh::lean_ctor_get(v___x_2025_, 4);
                    v_messages_2031_ = leanh::lean_ctor_get(v___x_2025_, 6);
                    v_infoState_2032_ = leanh::lean_ctor_get(v___x_2025_, 7);
                    v_snapshotTasks_2033_ = leanh::lean_ctor_get(v___x_2025_, 8);
                    v_isSharedCheck_2045_ = (!leanh::lean_is_exclusive(v___x_2025_)) as u8;
                    if v_isSharedCheck_2045_ == 0 {
                        v_unused_2046_ = leanh::lean_ctor_get(v___x_2025_, 5);
                        leanh::lean_dec(v_unused_2046_);
                        v___x_2035_ = v___x_2025_;
                        v_isShared_2036_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snapshotTasks_2033_);
                        leanh::lean_inc(v_infoState_2032_);
                        leanh::lean_inc(v_messages_2031_);
                        leanh::lean_inc(v_traceState_2030_);
                        leanh::lean_inc(v_auxDeclNGen_2029_);
                        leanh::lean_inc(v_ngen_2028_);
                        leanh::lean_inc(v_nextMacroScope_2027_);
                        leanh::lean_inc(v_env_2026_);
                        leanh::lean_dec(v___x_2025_);
                        v___x_2035_ = leanh::lean_box(0);
                        v_isShared_2036_ = v_isSharedCheck_2045_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_funIndName_2021_);
                    leanh::lean_dec_ref(v_funIndInfo_2015_);
                    v___x_2047_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__6_once),
                        _init_l_Lean_Meta_setFunIndInfo___closed__6,
                    );
                    v___x_2048_ = l_panic___at___00Lean_Meta_setFunIndInfo_spec__0(
                        v___x_2047_,
                        v_a_2016_,
                        v_a_2017_,
                    );
                    return v___x_2048_;
                }
            }
            1 => {
                v___x_2037_ = l_Lean_MapDeclarationExtension_insert___redArg(
                    v___x_2023_,
                    v_env_2026_,
                    v_funIndName_2021_,
                    v_funIndInfo_2015_,
                );
                v___x_2038_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_setFunIndInfo___closed__2_once),
                    _init_l_Lean_Meta_setFunIndInfo___closed__2,
                );
                if v_isShared_2036_ == 0 {
                    leanh::lean_ctor_set(v___x_2035_, 5, v___x_2038_);
                    leanh::lean_ctor_set(v___x_2035_, 0, v___x_2037_);
                    v___x_2040_ = v___x_2035_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2037_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_nextMacroScope_2027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_ngen_2028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 3, v_auxDeclNGen_2029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 4, v_traceState_2030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 5, v___x_2038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 6, v_messages_2031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 7, v_infoState_2032_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2044_, 8, v_snapshotTasks_2033_);
                    v___x_2040_ = v_reuseFailAlloc_2044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2041_ = lean_st_ref_set(v_a_2017_, v___x_2040_);
                v___x_2042_ = leanh::lean_box(0);
                v___x_2043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2043_, 0, v___x_2042_);
                return v___x_2043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_setFunIndInfo___boxed(
    mut v_funIndInfo_2049_: *mut leanh::LeanObject,
    mut v_a_2050_: *mut leanh::LeanObject,
    mut v_a_2051_: *mut leanh::LeanObject,
    mut v_a_2052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2053_ = l_Lean_Meta_setFunIndInfo(v_funIndInfo_2049_, v_a_2050_, v_a_2051_);
    leanh::lean_dec(v_a_2051_);
    leanh::lean_dec_ref(v_a_2050_);
    return v_res_2053_;
}
pub unsafe fn l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(
    mut v_inductName_2054_: *mut leanh::LeanObject,
    mut v_a_2055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2057_ = lean_st_ref_get(v_a_2055_);
    v_env_2058_ = leanh::lean_ctor_get(v___x_2057_, 0);
    leanh::lean_inc_ref(v_env_2058_);
    leanh::lean_dec(v___x_2057_);
    v___x_2059_ = l_Lean_Meta_funIndInfoExt;
    v_toEnvExtension_2060_ = leanh::lean_ctor_get(v___x_2059_, 0);
    v_asyncMode_2061_ = leanh::lean_ctor_get(v_toEnvExtension_2060_, 2);
    v___x_2062_ = l_Lean_Meta_instInhabitedFunIndInfo_default;
    v___x_2063_ = 0;
    v___x_2064_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(
        v___x_2062_,
        v___x_2059_,
        v_env_2058_,
        v_inductName_2054_,
        v_asyncMode_2061_,
        v___x_2063_,
    );
    v___x_2065_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2065_, 0, v___x_2064_);
    return v___x_2065_;
}
pub unsafe fn l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg___boxed(
    mut v_inductName_2066_: *mut leanh::LeanObject,
    mut v_a_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_2066_, v_a_2067_);
    leanh::lean_dec(v_a_2067_);
    return v_res_2069_;
}
pub unsafe fn l_Lean_Meta_getFunIndInfoForInduct_x3f(
    mut v_inductName_2070_: *mut leanh::LeanObject,
    mut v_a_2071_: *mut leanh::LeanObject,
    mut v_a_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_inductName_2070_, v_a_2072_);
    return v___x_2074_;
}
pub unsafe fn l_Lean_Meta_getFunIndInfoForInduct_x3f___boxed(
    mut v_inductName_2075_: *mut leanh::LeanObject,
    mut v_a_2076_: *mut leanh::LeanObject,
    mut v_a_2077_: *mut leanh::LeanObject,
    mut v_a_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_Meta_getFunIndInfoForInduct_x3f(v_inductName_2075_, v_a_2076_, v_a_2077_);
    leanh::lean_dec(v_a_2077_);
    leanh::lean_dec_ref(v_a_2076_);
    return v_res_2079_;
}
pub unsafe fn l_Lean_Meta_getFunIndInfo_x3f(
    mut v_cases_2080_: u8,
    mut v_unfolding_2081_: u8,
    mut v_funName_2082_: *mut leanh::LeanObject,
    mut v_a_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v_val_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut v_a_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2086_ = l_Lean_Meta_getFunInduct_x3f(
                    v_unfolding_2081_,
                    v_cases_2080_,
                    v_funName_2082_,
                    v_a_2083_,
                    v_a_2084_,
                );
                if leanh::lean_obj_tag(v___x_2086_) == 0 {
                    v_a_2087_ = leanh::lean_ctor_get(v___x_2086_, 0);
                    v_isSharedCheck_2097_ = (!leanh::lean_is_exclusive(v___x_2086_)) as u8;
                    if v_isSharedCheck_2097_ == 0 {
                        v___x_2089_ = v___x_2086_;
                        v_isShared_2090_ = v_isSharedCheck_2097_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2087_);
                        leanh::lean_dec(v___x_2086_);
                        v___x_2089_ = leanh::lean_box(0);
                        v_isShared_2090_ = v_isSharedCheck_2097_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2098_ = leanh::lean_ctor_get(v___x_2086_, 0);
                    v_isSharedCheck_2105_ = (!leanh::lean_is_exclusive(v___x_2086_)) as u8;
                    if v_isSharedCheck_2105_ == 0 {
                        v___x_2100_ = v___x_2086_;
                        v_isShared_2101_ = v_isSharedCheck_2105_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2098_);
                        leanh::lean_dec(v___x_2086_);
                        v___x_2100_ = leanh::lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2105_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2087_) == 1 {
                    leanh::lean_del_object(v___x_2089_);
                    v_val_2091_ = leanh::lean_ctor_get(v_a_2087_, 0);
                    leanh::lean_inc(v_val_2091_);
                    leanh::lean_dec_ref_known(v_a_2087_, 1);
                    v___x_2092_ =
                        l_Lean_Meta_getFunIndInfoForInduct_x3f___redArg(v_val_2091_, v_a_2084_);
                    return v___x_2092_;
                } else {
                    leanh::lean_dec(v_a_2087_);
                    v___x_2093_ = leanh::lean_box(0);
                    if v_isShared_2090_ == 0 {
                        leanh::lean_ctor_set(v___x_2089_, 0, v___x_2093_);
                        v___x_2095_ = v___x_2089_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2096_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
                        v___x_2095_ = v_reuseFailAlloc_2096_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2095_;
            }
            3 => {
                if v_isShared_2101_ == 0 {
                    v___x_2103_ = v___x_2100_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_a_2098_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFunIndInfo_x3f___boxed(
    mut v_cases_2106_: *mut leanh::LeanObject,
    mut v_unfolding_2107_: *mut leanh::LeanObject,
    mut v_funName_2108_: *mut leanh::LeanObject,
    mut v_a_2109_: *mut leanh::LeanObject,
    mut v_a_2110_: *mut leanh::LeanObject,
    mut v_a_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cases_boxed_2112_: u8 = 0;
    let mut v_unfolding_boxed_2113_: u8 = 0;
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cases_boxed_2112_ = (leanh::lean_unbox(v_cases_2106_) as u8);
    v_unfolding_boxed_2113_ = (leanh::lean_unbox(v_unfolding_2107_) as u8);
    v_res_2114_ = l_Lean_Meta_getFunIndInfo_x3f(
        v_cases_boxed_2112_,
        v_unfolding_boxed_2113_,
        v_funName_2108_,
        v_a_2109_,
        v_a_2110_,
    );
    leanh::lean_dec(v_a_2110_);
    leanh::lean_dec_ref(v_a_2109_);
    return v_res_2114_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_FunIndInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ReservedNameAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedFunIndParamKind_default =
        _init_l_Lean_Meta_instInhabitedFunIndParamKind_default();
    l_Lean_Meta_instInhabitedFunIndParamKind = _init_l_Lean_Meta_instInhabitedFunIndParamKind();
    res = l___private_Lean_Meta_Tactic_FunIndInfo_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_FunIndInfo_2193198776____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_funIndInfoExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_funIndInfoExt);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_FunIndInfo(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_FunIndInfo(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ReservedNameAction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_FunIndInfo(builtin);
}