// Lean compiler output
// Module: Lean.Meta.CoeAttr
// Imports: Lean.Meta.FunInfo
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isExplicit, l_Lean_mkApp3, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::Meta::FunInfo::{
    initialize_Lean_Meta_FunInfo, l_Lean_Meta_getFunInfo, runtime_initialize_Lean_Meta_FunInfo,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    l_Lean_ScopedEnvExtension_addEntry___redArg, l_Lean_ScopedEnvExtension_getState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static mut l_Lean_Meta_instInhabitedCoeFnType_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedCoeFnType: u8 = 0;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__0_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101, 46,
        99, 111, 101, 0,
    ],
};
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__2_value: crate::leanh::LeanStringObject<
    27,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101, 46,
        99, 111, 101, 70, 117, 110, 0,
    ],
};
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__4_value: crate::leanh::LeanStringObject<
    28,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101, 46,
        99, 111, 101, 83, 111, 114, 116, 0,
    ],
};
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__5_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__4_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCoeFnType_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCoeFnType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReprCoeFnType: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 111, 101, 70, 110, 84, 121, 112, 101, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 111, 101, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2813220318977726453 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12556370647174111156 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [99, 111, 101, 70, 117, 110, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2813220318977726453 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        16398515986243675126 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 101, 83, 111, 114, 116, 0],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        2813220318977726453 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value)
            as *mut crate::leanh::LeanObject,
        9442608608187171560 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instToExprCoeFnType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instToExprCoeFnType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15449383196166861506 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnType___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
            2813220318977726453 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instToExprCoeFnType___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instToExprCoeFnType: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        0 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCoeFnInfo_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instInhabitedCoeFnInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value:
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [110, 117, 109, 65, 114, 103, 115, 0],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value:
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value:
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
    m_data: [44, 0],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 101, 114, 99, 101, 101, 0],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value:
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
    m_data: [116, 121, 112, 101, 0],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value:
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCoeFnInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCoeFnInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_instReprCoeFnInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [67, 111, 101, 70, 110, 73, 110, 102, 111, 0],
};
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value:
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
    m_data: [109, 107, 0],
};
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        1996622761251820373 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        3253084188537368017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instToExprCoeFnInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            15449383196166861506 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            1996622761251820373 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_instToExprCoeFnInfo: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,15884443959248703457 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerCoercion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerCoercion___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerCoercion___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerCoercion___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_registerCoercion___closed__4_value: crate::leanh::LeanStringObject<27> =
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
            32, 104, 97, 115, 32, 110, 111, 32, 101, 120, 112, 108, 105, 99, 105, 116, 32, 97, 114,
            103, 117, 109, 101, 110, 116, 115, 0,
        ],
    };
static mut l_Lean_Meta_registerCoercion___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_registerCoercion___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_registerCoercion___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_registerCoercion___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13556645696814629918 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5248179736981678329 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16576108964040073180 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,10567757556072296701 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,14400173562802066965 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7648651235586661436 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2060747640412624181 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,12647287533329886112 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,16861913366284030220 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,5178666544776117203 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value) as *mut crate::leanh::LeanObject,18011328033297698546 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<3> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [65, 100, 100, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 99, 111, 101, 114, 99, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CoeFnType_ctorIdx(mut v_x_1271_: u8) -> *mut crate::leanh::LeanObject {
    match v_x_1271_ {
        0 => {
            let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1272_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1272_;
        }
        1 => {
            let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1273_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1273_;
        }
        _ => {
            let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1274_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1274_;
        }
    }
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorIdx___boxed(
    mut v_x_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1276_ = (crate::leanh::lean_unbox(v_x_1275_) as u8);
    v_res_1277_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_boxed_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_toCtorIdx(mut v_x_1278_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_toCtorIdx___boxed(
    mut v_x_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1281_: u8 = 0;
    let mut v_res_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1281_ = (crate::leanh::lean_unbox(v_x_1280_) as u8);
    v_res_1282_ = l_Lean_Meta_CoeFnType_toCtorIdx(v_x_4__boxed_1281_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___redArg(
    mut v_k_1283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1283_);
    return v_k_1283_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___redArg___boxed(
    mut v_k_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Meta_CoeFnType_ctorElim___redArg(v_k_1284_);
    crate::leanh::lean_dec(v_k_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim(
    mut v_motive_1286_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1287_: *mut crate::leanh::LeanObject,
    mut v_t_1288_: u8,
    mut v_h_1289_: *mut crate::leanh::LeanObject,
    mut v_k_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1290_);
    return v_k_1290_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___boxed(
    mut v_motive_1291_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1292_: *mut crate::leanh::LeanObject,
    mut v_t_1293_: *mut crate::leanh::LeanObject,
    mut v_h_1294_: *mut crate::leanh::LeanObject,
    mut v_k_1295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1296_ = (crate::leanh::lean_unbox(v_t_1293_) as u8);
    v_res_1297_ = l_Lean_Meta_CoeFnType_ctorElim(
        v_motive_1291_,
        v_ctorIdx_1292_,
        v_t_boxed_1296_,
        v_h_1294_,
        v_k_1295_,
    );
    crate::leanh::lean_dec(v_k_1295_);
    crate::leanh::lean_dec(v_ctorIdx_1292_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___redArg(
    mut v_coe_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coe_1298_);
    return v_coe_1298_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___redArg___boxed(
    mut v_coe_1299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Meta_CoeFnType_coe_elim___redArg(v_coe_1299_);
    crate::leanh::lean_dec(v_coe_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim(
    mut v_motive_1301_: *mut crate::leanh::LeanObject,
    mut v_t_1302_: u8,
    mut v_h_1303_: *mut crate::leanh::LeanObject,
    mut v_coe_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coe_1304_);
    return v_coe_1304_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___boxed(
    mut v_motive_1305_: *mut crate::leanh::LeanObject,
    mut v_t_1306_: *mut crate::leanh::LeanObject,
    mut v_h_1307_: *mut crate::leanh::LeanObject,
    mut v_coe_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1309_ = (crate::leanh::lean_unbox(v_t_1306_) as u8);
    v_res_1310_ =
        l_Lean_Meta_CoeFnType_coe_elim(v_motive_1305_, v_t_boxed_1309_, v_h_1307_, v_coe_1308_);
    crate::leanh::lean_dec(v_coe_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___redArg(
    mut v_coeFun_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coeFun_1311_);
    return v_coeFun_1311_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___redArg___boxed(
    mut v_coeFun_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_Meta_CoeFnType_coeFun_elim___redArg(v_coeFun_1312_);
    crate::leanh::lean_dec(v_coeFun_1312_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim(
    mut v_motive_1314_: *mut crate::leanh::LeanObject,
    mut v_t_1315_: u8,
    mut v_h_1316_: *mut crate::leanh::LeanObject,
    mut v_coeFun_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coeFun_1317_);
    return v_coeFun_1317_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___boxed(
    mut v_motive_1318_: *mut crate::leanh::LeanObject,
    mut v_t_1319_: *mut crate::leanh::LeanObject,
    mut v_h_1320_: *mut crate::leanh::LeanObject,
    mut v_coeFun_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1322_: u8 = 0;
    let mut v_res_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1322_ = (crate::leanh::lean_unbox(v_t_1319_) as u8);
    v_res_1323_ = l_Lean_Meta_CoeFnType_coeFun_elim(
        v_motive_1318_,
        v_t_boxed_1322_,
        v_h_1320_,
        v_coeFun_1321_,
    );
    crate::leanh::lean_dec(v_coeFun_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___redArg(
    mut v_coeSort_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coeSort_1324_);
    return v_coeSort_1324_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___redArg___boxed(
    mut v_coeSort_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Meta_CoeFnType_coeSort_elim___redArg(v_coeSort_1325_);
    crate::leanh::lean_dec(v_coeSort_1325_);
    return v_res_1326_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim(
    mut v_motive_1327_: *mut crate::leanh::LeanObject,
    mut v_t_1328_: u8,
    mut v_h_1329_: *mut crate::leanh::LeanObject,
    mut v_coeSort_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_coeSort_1330_);
    return v_coeSort_1330_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___boxed(
    mut v_motive_1331_: *mut crate::leanh::LeanObject,
    mut v_t_1332_: *mut crate::leanh::LeanObject,
    mut v_h_1333_: *mut crate::leanh::LeanObject,
    mut v_coeSort_1334_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1335_: u8 = 0;
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1335_ = (crate::leanh::lean_unbox(v_t_1332_) as u8);
    v_res_1336_ = l_Lean_Meta_CoeFnType_coeSort_elim(
        v_motive_1331_,
        v_t_boxed_1335_,
        v_h_1333_,
        v_coeSort_1334_,
    );
    crate::leanh::lean_dec(v_coeSort_1334_);
    return v_res_1336_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCoeFnType_default() -> u8 {
    let mut v___x_1337_: u8 = 0;
    v___x_1337_ = 0;
    return v___x_1337_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedCoeFnType() -> u8 {
    let mut v___x_1338_: u8 = 0;
    v___x_1338_ = 0;
    return v___x_1338_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1348_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1349_ = lean_nat_to_int(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1350_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1351_ = lean_nat_to_int(v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnType_repr(
    mut v_x_1352_: u8,
    mut v_prec_1353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1352_ {
                0 => {
                    v___x_1375_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1376_ = lean_nat_dec_le(v___x_1375_, v_prec_1353_);
                    if v___x_1376_ == 0 {
                        v___x_1377_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6,
                        );
                        v___y_1355_ = v___x_1377_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1378_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7,
                        );
                        v___y_1355_ = v___x_1378_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1379_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1380_ = lean_nat_dec_le(v___x_1379_, v_prec_1353_);
                    if v___x_1380_ == 0 {
                        v___x_1381_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6,
                        );
                        v___y_1362_ = v___x_1381_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1382_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7,
                        );
                        v___y_1362_ = v___x_1382_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1383_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_1384_ = lean_nat_dec_le(v___x_1383_, v_prec_1353_);
                    if v___x_1384_ == 0 {
                        v___x_1385_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__6_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6,
                        );
                        v___y_1369_ = v___x_1385_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1386_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnType_repr___closed__7),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_instReprCoeFnType_repr___closed__7_once
                            ),
                            _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7,
                        );
                        v___y_1369_ = v___x_1386_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1356_ = l_Lean_Meta_instReprCoeFnType_repr___closed__1;
                crate::leanh::lean_inc(v___y_1355_);
                v___x_1357_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1357_, 0, v___y_1355_);
                crate::leanh::lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                v___x_1358_ = 0;
                v___x_1359_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1357_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1359_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1358_,
                );
                v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1353_);
                return v___x_1360_;
            }
            2 => {
                v___x_1363_ = l_Lean_Meta_instReprCoeFnType_repr___closed__3;
                crate::leanh::lean_inc(v___y_1362_);
                v___x_1364_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1364_, 0, v___y_1362_);
                crate::leanh::lean_ctor_set(v___x_1364_, 1, v___x_1363_);
                v___x_1365_ = 0;
                v___x_1366_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1364_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1366_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1365_,
                );
                v___x_1367_ = l_Repr_addAppParen(v___x_1366_, v_prec_1353_);
                return v___x_1367_;
            }
            3 => {
                v___x_1370_ = l_Lean_Meta_instReprCoeFnType_repr___closed__5;
                crate::leanh::lean_inc(v___y_1369_);
                v___x_1371_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1371_, 0, v___y_1369_);
                crate::leanh::lean_ctor_set(v___x_1371_, 1, v___x_1370_);
                v___x_1372_ = 0;
                v___x_1373_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1373_, 0, v___x_1371_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1373_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1372_,
                );
                v___x_1374_ = l_Repr_addAppParen(v___x_1373_, v_prec_1353_);
                return v___x_1374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_instReprCoeFnType_repr___boxed(
    mut v_x_1387_: *mut crate::leanh::LeanObject,
    mut v_prec_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_177__boxed_1389_: u8 = 0;
    let mut v_res_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1389_ = (crate::leanh::lean_unbox(v_x_1387_) as u8);
    v_res_1390_ = l_Lean_Meta_instReprCoeFnType_repr(v_x_177__boxed_1389_, v_prec_1388_);
    crate::leanh::lean_dec(v_prec_1388_);
    return v_res_1390_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ofNat(mut v_n_1393_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    v___x_1394_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1395_ = lean_nat_dec_le(v_n_1393_, v___x_1394_);
    if v___x_1395_ == 0 {
        let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1397_: u8 = 0;
        v___x_1396_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1397_ = lean_nat_dec_le(v_n_1393_, v___x_1396_);
        if v___x_1397_ == 0 {
            let mut v___x_1398_: u8 = 0;
            v___x_1398_ = 2;
            return v___x_1398_;
        } else {
            let mut v___x_1399_: u8 = 0;
            v___x_1399_ = 1;
            return v___x_1399_;
        }
    } else {
        let mut v___x_1400_: u8 = 0;
        v___x_1400_ = 0;
        return v___x_1400_;
    }
}
pub unsafe fn l_Lean_Meta_CoeFnType_ofNat___boxed(
    mut v_n_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1402_: u8 = 0;
    let mut v_r_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Meta_CoeFnType_ofNat(v_n_1401_);
    crate::leanh::lean_dec(v_n_1401_);
    v_r_1403_ = crate::leanh::lean_box((v_res_1402_) as usize);
    return v_r_1403_;
}
pub unsafe fn l_Lean_Meta_instDecidableEqCoeFnType(mut v_x_1404_: u8, mut v_y_1405_: u8) -> u8 {
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    v___x_1406_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_1404_);
    v___x_1407_ = l_Lean_Meta_CoeFnType_ctorIdx(v_y_1405_);
    v___x_1408_ = lean_nat_dec_eq(v___x_1406_, v___x_1407_);
    crate::leanh::lean_dec(v___x_1407_);
    crate::leanh::lean_dec(v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_Meta_instDecidableEqCoeFnType___boxed(
    mut v_x_1409_: *mut crate::leanh::LeanObject,
    mut v_y_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_13__boxed_1411_: u8 = 0;
    let mut v_y_14__boxed_1412_: u8 = 0;
    let mut v_res_1413_: u8 = 0;
    let mut v_r_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_13__boxed_1411_ = (crate::leanh::lean_unbox(v_x_1409_) as u8);
    v_y_14__boxed_1412_ = (crate::leanh::lean_unbox(v_y_1410_) as u8);
    v_res_1413_ = l_Lean_Meta_instDecidableEqCoeFnType(v_x_13__boxed_1411_, v_y_14__boxed_1412_);
    v_r_1414_ = crate::leanh::lean_box((v_res_1413_) as usize);
    return v_r_1414_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = crate::leanh::lean_box(0);
    v___x_1425_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4;
    v___x_1426_ = l_Lean_mkConst(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_box(0);
    v___x_1434_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7;
    v___x_1435_ = l_Lean_mkConst(v___x_1434_, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = crate::leanh::lean_box(0);
    v___x_1443_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10;
    v___x_1444_ = l_Lean_mkConst(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnType___lam__0(
    mut v_x_1445_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1445_ {
        0 => {
            let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1446_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5,
            );
            return v___x_1446_;
        }
        1 => {
            let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1447_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8,
            );
            return v___x_1447_;
        }
        _ => {
            let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1448_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11,
            );
            return v___x_1448_;
        }
    }
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnType___lam__0___boxed(
    mut v_x_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_156__boxed_1450_: u8 = 0;
    let mut v_res_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_156__boxed_1450_ = (crate::leanh::lean_unbox(v_x_1449_) as u8);
    v_res_1451_ = l_Lean_Meta_instToExprCoeFnType___lam__0(v_x_156__boxed_1450_);
    return v_res_1451_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = crate::leanh::lean_box(0);
    v___x_1458_ = l_Lean_Meta_instToExprCoeFnType___closed__1;
    v___x_1459_ = l_Lean_mkConst(v___x_1458_, v___x_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1460_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__2_once),
        _init_l_Lean_Meta_instToExprCoeFnType___closed__2,
    );
    v___f_1461_ = l_Lean_Meta_instToExprCoeFnType___closed__0;
    v___x_1462_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1462_, 0, v___f_1461_);
    crate::leanh::lean_ctor_set(v___x_1462_, 1, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType() -> *mut crate::leanh::LeanObject {
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnType___closed__3,
    );
    return v___x_1463_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_instReprCoeFnInfo_repr_spec__0(
    mut v_a_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1470_ = lean_nat_to_int(v_a_1469_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1484_ = crate::leanh::lean_unsigned_to_nat(11);
    v___x_1485_ = lean_nat_to_int(v___x_1484_);
    return v___x_1485_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1495_ = crate::leanh::lean_unsigned_to_nat(8);
    v___x_1496_ = lean_nat_to_int(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0;
    v___x_1499_ = lean_string_length(v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16,
    );
    v___x_1501_ = lean_nat_to_int(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr___redArg(
    mut v_x_1506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_coercee_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1509_: u8 = 0;
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numArgs_1507_ = crate::leanh::lean_ctor_get(v_x_1506_, 0);
    crate::leanh::lean_inc(v_numArgs_1507_);
    v_coercee_1508_ = crate::leanh::lean_ctor_get(v_x_1506_, 1);
    crate::leanh::lean_inc(v_coercee_1508_);
    v_type_1509_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1506_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_x_1506_);
    v___x_1510_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5;
    v___x_1511_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6;
    v___x_1512_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7,
    );
    v___x_1513_ = l_Nat_reprFast(v_numArgs_1507_);
    v___x_1514_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    v___x_1515_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1515_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1515_, 1, v___x_1514_);
    v___x_1516_ = 0;
    v___x_1517_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1517_, 0, v___x_1515_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1517_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1518_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1511_);
    crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
    v___x_1519_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9;
    v___x_1520_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1518_);
    crate::leanh::lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    v___x_1521_ = crate::leanh::lean_box(1);
    v___x_1522_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1522_, 0, v___x_1520_);
    crate::leanh::lean_ctor_set(v___x_1522_, 1, v___x_1521_);
    v___x_1523_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11;
    v___x_1524_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1524_, 0, v___x_1522_);
    crate::leanh::lean_ctor_set(v___x_1524_, 1, v___x_1523_);
    v___x_1525_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1525_, 0, v___x_1524_);
    crate::leanh::lean_ctor_set(v___x_1525_, 1, v___x_1510_);
    v___x_1526_ = l_Nat_reprFast(v_coercee_1508_);
    v___x_1527_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    v___x_1528_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1528_, 0, v___x_1512_);
    crate::leanh::lean_ctor_set(v___x_1528_, 1, v___x_1527_);
    v___x_1529_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1528_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1529_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1530_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1525_);
    crate::leanh::lean_ctor_set(v___x_1530_, 1, v___x_1529_);
    v___x_1531_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1519_);
    v___x_1532_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
    crate::leanh::lean_ctor_set(v___x_1532_, 1, v___x_1521_);
    v___x_1533_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13;
    v___x_1534_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1534_, 0, v___x_1532_);
    crate::leanh::lean_ctor_set(v___x_1534_, 1, v___x_1533_);
    v___x_1535_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    crate::leanh::lean_ctor_set(v___x_1535_, 1, v___x_1510_);
    v___x_1536_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14,
    );
    v___x_1537_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1538_ = l_Lean_Meta_instReprCoeFnType_repr(v_type_1509_, v___x_1537_);
    v___x_1539_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1539_, 0, v___x_1536_);
    crate::leanh::lean_ctor_set(v___x_1539_, 1, v___x_1538_);
    v___x_1540_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1540_, 0, v___x_1539_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1540_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1541_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1535_);
    crate::leanh::lean_ctor_set(v___x_1541_, 1, v___x_1540_);
    v___x_1542_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17,
    );
    v___x_1543_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18;
    v___x_1544_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1544_, 0, v___x_1543_);
    crate::leanh::lean_ctor_set(v___x_1544_, 1, v___x_1541_);
    v___x_1545_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19;
    v___x_1546_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1546_, 0, v___x_1544_);
    crate::leanh::lean_ctor_set(v___x_1546_, 1, v___x_1545_);
    v___x_1547_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1542_);
    crate::leanh::lean_ctor_set(v___x_1547_, 1, v___x_1546_);
    v___x_1548_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1547_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1548_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    return v___x_1548_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr(
    mut v_x_1549_: *mut crate::leanh::LeanObject,
    mut v_prec_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg(v_x_1549_);
    return v___x_1551_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr___boxed(
    mut v_x_1552_: *mut crate::leanh::LeanObject,
    mut v_prec_1553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Lean_Meta_instReprCoeFnInfo_repr(v_x_1552_, v_prec_1553_);
    crate::leanh::lean_dec(v_prec_1553_);
    return v_res_1554_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1564_ = crate::leanh::lean_box(0);
    v___x_1565_ = l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2;
    v___x_1566_ = l_Lean_mkConst(v___x_1565_, v___x_1564_);
    return v___x_1566_;
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnInfo___lam__0(
    mut v_x_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_coercee_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1570_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_numArgs_1568_ = crate::leanh::lean_ctor_get(v_x_1567_, 0);
    crate::leanh::lean_inc(v_numArgs_1568_);
    v_coercee_1569_ = crate::leanh::lean_ctor_get(v_x_1567_, 1);
    crate::leanh::lean_inc(v_coercee_1569_);
    v_type_1570_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1567_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    crate::leanh::lean_dec_ref(v_x_1567_);
    v___x_1571_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3,
    );
    v___x_1572_ = l_Lean_mkNatLit(v_numArgs_1568_);
    v___x_1573_ = l_Lean_mkNatLit(v_coercee_1569_);
    match v_type_1570_ {
        0 => {
            let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1574_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5,
            );
            v___x_1575_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1574_);
            return v___x_1575_;
        }
        1 => {
            let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1576_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8,
            );
            v___x_1577_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1576_);
            return v___x_1577_;
        }
        _ => {
            let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1578_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11,
            );
            v___x_1579_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1578_);
            return v___x_1579_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = crate::leanh::lean_box(0);
    v___x_1586_ = l_Lean_Meta_instToExprCoeFnInfo___closed__1;
    v___x_1587_ = l_Lean_mkConst(v___x_1586_, v___x_1585_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1588_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__2_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2,
    );
    v___f_1589_ = l_Lean_Meta_instToExprCoeFnInfo___closed__0;
    v___x_1590_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1590_, 0, v___f_1589_);
    crate::leanh::lean_ctor_set(v___x_1590_, 1, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo() -> *mut crate::leanh::LeanObject {
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3,
    );
    return v___x_1591_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v_st_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_1594_ = crate::leanh::lean_ctor_get(v_x_1593_, 0);
    crate::leanh::lean_inc(v_fst_1594_);
    v_snd_1595_ = crate::leanh::lean_ctor_get(v_x_1593_, 1);
    crate::leanh::lean_inc(v_snd_1595_);
    crate::leanh::lean_dec_ref(v_x_1593_);
    v___x_1596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_1594_,
        v_snd_1595_,
        v_st_1592_,
    );
    return v___x_1596_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v_x_1597_: *mut crate::leanh::LeanObject,
    mut v_a_1598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1599_, 0, v_a_1598_);
    crate::leanh::lean_inc_ref_n(v___x_1599_, 2);
    v___x_1600_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
    crate::leanh::lean_ctor_set(v___x_1600_, 1, v___x_1599_);
    crate::leanh::lean_ctor_set(v___x_1600_, 2, v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v_x_1601_: *mut crate::leanh::LeanObject,
    mut v_a_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_1601_, v_a_1602_);
    crate::leanh::lean_dec_ref(v_x_1601_);
    return v_res_1603_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v___y_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___y_1604_);
    return v___y_1604_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v___y_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___y_1605_);
    crate::leanh::lean_dec(v___y_1605_);
    return v_res_1606_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_;
    v___x_1623_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v_a_1624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1625_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
    return v_res_1625_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___redArg(
    mut v_fn_1626_: *mut crate::leanh::LeanObject,
    mut v_a_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1629_ = lean_st_ref_get(v_a_1627_);
    v_env_1630_ = crate::leanh::lean_ctor_get(v___x_1629_, 0);
    crate::leanh::lean_inc_ref(v_env_1630_);
    crate::leanh::lean_dec(v___x_1629_);
    v___x_1631_ = l_Lean_Meta_coeExt;
    v_ext_1632_ = crate::leanh::lean_ctor_get(v___x_1631_, 1);
    v_toEnvExtension_1633_ = crate::leanh::lean_ctor_get(v_ext_1632_, 0);
    v_asyncMode_1634_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1633_, 2);
    v___x_1635_ = crate::leanh::lean_box(1);
    v___x_1636_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_1635_,
        v___x_1631_,
        v_env_1630_,
        v_asyncMode_1634_,
    );
    v___x_1637_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1636_,
            v_fn_1626_,
        );
    crate::leanh::lean_dec(v___x_1636_);
    v___x_1638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(
    mut v_fn_1639_: *mut crate::leanh::LeanObject,
    mut v_a_1640_: *mut crate::leanh::LeanObject,
    mut v_a_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_1639_, v_a_1640_);
    crate::leanh::lean_dec(v_a_1640_);
    crate::leanh::lean_dec(v_fn_1639_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f(
    mut v_fn_1643_: *mut crate::leanh::LeanObject,
    mut v_a_1644_: *mut crate::leanh::LeanObject,
    mut v_a_1645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_1643_, v_a_1645_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___boxed(
    mut v_fn_1648_: *mut crate::leanh::LeanObject,
    mut v_a_1649_: *mut crate::leanh::LeanObject,
    mut v_a_1650_: *mut crate::leanh::LeanObject,
    mut v_a_1651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_Meta_getCoeFnInfo_x3f(v_fn_1648_, v_a_1649_, v_a_1650_);
    crate::leanh::lean_dec(v_a_1650_);
    crate::leanh::lean_dec_ref(v_a_1649_);
    crate::leanh::lean_dec(v_fn_1648_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(
    mut v_msgData_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_st_ref_get(v___y_1657_);
    v_env_1660_ = crate::leanh::lean_ctor_get(v___x_1659_, 0);
    crate::leanh::lean_inc_ref(v_env_1660_);
    crate::leanh::lean_dec(v___x_1659_);
    v___x_1661_ = lean_st_ref_get(v___y_1655_);
    v_mctx_1662_ = crate::leanh::lean_ctor_get(v___x_1661_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1662_);
    crate::leanh::lean_dec(v___x_1661_);
    v_lctx_1663_ = crate::leanh::lean_ctor_get(v___y_1654_, 2);
    v_options_1664_ = crate::leanh::lean_ctor_get(v___y_1656_, 2);
    crate::leanh::lean_inc_ref(v_options_1664_);
    crate::leanh::lean_inc_ref(v_lctx_1663_);
    v___x_1665_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1665_, 0, v_env_1660_);
    crate::leanh::lean_ctor_set(v___x_1665_, 1, v_mctx_1662_);
    crate::leanh::lean_ctor_set(v___x_1665_, 2, v_lctx_1663_);
    crate::leanh::lean_ctor_set(v___x_1665_, 3, v_options_1664_);
    v___x_1666_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1666_, 0, v___x_1665_);
    crate::leanh::lean_ctor_set(v___x_1666_, 1, v_msgData_1653_);
    v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4___boxed(
    mut v_msgData_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msgData_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    crate::leanh::lean_dec(v___y_1672_);
    crate::leanh::lean_dec_ref(v___y_1671_);
    crate::leanh::lean_dec(v___y_1670_);
    crate::leanh::lean_dec_ref(v___y_1669_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
    mut v_msg_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
    mut v___y_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1681_ = crate::leanh::lean_ctor_get(v___y_1678_, 5);
                v___x_1682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
                v_a_1683_ = crate::leanh::lean_ctor_get(v___x_1682_, 0);
                v_isSharedCheck_1691_ = (!crate::leanh::lean_is_exclusive(v___x_1682_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1685_ = v___x_1682_;
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1683_);
                    crate::leanh::lean_dec(v___x_1682_);
                    v___x_1685_ = crate::leanh::lean_box(0);
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1681_);
                v___x_1687_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1687_, 0, v_ref_1681_);
                crate::leanh::lean_ctor_set(v___x_1687_, 1, v_a_1683_);
                if v_isShared_1686_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1685_, 1);
                    crate::leanh::lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1689_ = v___x_1685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
                    v___x_1689_ = v_reuseFailAlloc_1690_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1689_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg___boxed(
    mut v_msg_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
        v_msg_1692_,
        v___y_1693_,
        v___y_1694_,
        v___y_1695_,
        v___y_1696_,
    );
    crate::leanh::lean_dec(v___y_1696_);
    crate::leanh::lean_dec_ref(v___y_1695_);
    crate::leanh::lean_dec(v___y_1694_);
    crate::leanh::lean_dec_ref(v___y_1693_);
    return v_res_1698_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(
    mut v_ref_1699_: *mut crate::leanh::LeanObject,
    mut v_msg_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
    mut v___y_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1718_: u8 = 0;
    let mut v_cancelTk_x3f_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1720_: u8 = 0;
    let mut v_inheritedTraceOptions_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1706_ = crate::leanh::lean_ctor_get(v___y_1703_, 0);
    v_fileMap_1707_ = crate::leanh::lean_ctor_get(v___y_1703_, 1);
    v_options_1708_ = crate::leanh::lean_ctor_get(v___y_1703_, 2);
    v_currRecDepth_1709_ = crate::leanh::lean_ctor_get(v___y_1703_, 3);
    v_maxRecDepth_1710_ = crate::leanh::lean_ctor_get(v___y_1703_, 4);
    v_ref_1711_ = crate::leanh::lean_ctor_get(v___y_1703_, 5);
    v_currNamespace_1712_ = crate::leanh::lean_ctor_get(v___y_1703_, 6);
    v_openDecls_1713_ = crate::leanh::lean_ctor_get(v___y_1703_, 7);
    v_initHeartbeats_1714_ = crate::leanh::lean_ctor_get(v___y_1703_, 8);
    v_maxHeartbeats_1715_ = crate::leanh::lean_ctor_get(v___y_1703_, 9);
    v_quotContext_1716_ = crate::leanh::lean_ctor_get(v___y_1703_, 10);
    v_currMacroScope_1717_ = crate::leanh::lean_ctor_get(v___y_1703_, 11);
    v_diag_1718_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1703_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1719_ = crate::leanh::lean_ctor_get(v___y_1703_, 12);
    v_suppressElabErrors_1720_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1703_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1721_ = crate::leanh::lean_ctor_get(v___y_1703_, 13);
    v_ref_1722_ = l_Lean_replaceRef(v_ref_1699_, v_ref_1711_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1721_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1719_);
    crate::leanh::lean_inc(v_currMacroScope_1717_);
    crate::leanh::lean_inc(v_quotContext_1716_);
    crate::leanh::lean_inc(v_maxHeartbeats_1715_);
    crate::leanh::lean_inc(v_initHeartbeats_1714_);
    crate::leanh::lean_inc(v_openDecls_1713_);
    crate::leanh::lean_inc(v_currNamespace_1712_);
    crate::leanh::lean_inc(v_maxRecDepth_1710_);
    crate::leanh::lean_inc(v_currRecDepth_1709_);
    crate::leanh::lean_inc_ref(v_options_1708_);
    crate::leanh::lean_inc_ref(v_fileMap_1707_);
    crate::leanh::lean_inc_ref(v_fileName_1706_);
    v___x_1723_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1723_, 0, v_fileName_1706_);
    crate::leanh::lean_ctor_set(v___x_1723_, 1, v_fileMap_1707_);
    crate::leanh::lean_ctor_set(v___x_1723_, 2, v_options_1708_);
    crate::leanh::lean_ctor_set(v___x_1723_, 3, v_currRecDepth_1709_);
    crate::leanh::lean_ctor_set(v___x_1723_, 4, v_maxRecDepth_1710_);
    crate::leanh::lean_ctor_set(v___x_1723_, 5, v_ref_1722_);
    crate::leanh::lean_ctor_set(v___x_1723_, 6, v_currNamespace_1712_);
    crate::leanh::lean_ctor_set(v___x_1723_, 7, v_openDecls_1713_);
    crate::leanh::lean_ctor_set(v___x_1723_, 8, v_initHeartbeats_1714_);
    crate::leanh::lean_ctor_set(v___x_1723_, 9, v_maxHeartbeats_1715_);
    crate::leanh::lean_ctor_set(v___x_1723_, 10, v_quotContext_1716_);
    crate::leanh::lean_ctor_set(v___x_1723_, 11, v_currMacroScope_1717_);
    crate::leanh::lean_ctor_set(v___x_1723_, 12, v_cancelTk_x3f_1719_);
    crate::leanh::lean_ctor_set(v___x_1723_, 13, v_inheritedTraceOptions_1721_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1723_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1718_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1723_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1720_,
    );
    v___x_1724_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
        v_msg_1700_,
        v___y_1701_,
        v___y_1702_,
        v___x_1723_,
        v___y_1704_,
    );
    crate::leanh::lean_dec_ref_known(v___x_1723_, 14);
    return v___x_1724_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_ref_1725_: *mut crate::leanh::LeanObject,
    mut v_msg_1726_: *mut crate::leanh::LeanObject,
    mut v___y_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
    mut v___y_1730_: *mut crate::leanh::LeanObject,
    mut v___y_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_1725_, v_msg_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
    crate::leanh::lean_dec(v___y_1730_);
    crate::leanh::lean_dec_ref(v___y_1729_);
    crate::leanh::lean_dec(v___y_1728_);
    crate::leanh::lean_dec_ref(v___y_1727_);
    crate::leanh::lean_dec(v_ref_1725_);
    return v_res_1732_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_1735_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1736_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_1737_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1738_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1738_, 0, v___x_1737_);
    crate::leanh::lean_ctor_set(v___x_1738_, 1, v___x_1737_);
    crate::leanh::lean_ctor_set(v___x_1738_, 2, v___x_1737_);
    crate::leanh::lean_ctor_set(v___x_1738_, 3, v___x_1737_);
    crate::leanh::lean_ctor_set(v___x_1738_, 4, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1738_, 5, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1738_, 6, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1738_, 7, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1738_, 8, v___x_1736_);
    crate::leanh::lean_ctor_set(v___x_1738_, 9, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1739_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1740_ = lean_mk_empty_array_with_capacity(v___x_1739_);
    v___x_1741_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1741_, 0, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1742_ = 5usize;
    v___x_1743_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1744_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1745_ = lean_mk_empty_array_with_capacity(v___x_1744_);
    v___x_1746_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_1747_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    crate::leanh::lean_ctor_set(v___x_1747_, 1, v___x_1745_);
    crate::leanh::lean_ctor_set(v___x_1747_, 2, v___x_1743_);
    crate::leanh::lean_ctor_set(v___x_1747_, 3, v___x_1743_);
    crate::leanh::lean_ctor_set_usize(v___x_1747_, 4, v___x_1742_);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1748_ = crate::leanh::lean_box(1);
    v___x_1749_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_1750_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_1751_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    crate::leanh::lean_ctor_set(v___x_1751_, 1, v___x_1749_);
    crate::leanh::lean_ctor_set(v___x_1751_, 2, v___x_1748_);
    return v___x_1751_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1753_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1759_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
    return v___x_1763_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_1773_: *mut crate::leanh::LeanObject,
    mut v_declHint_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v_isExporting_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1777_ = lean_st_ref_get(v___y_1775_);
                v_env_1778_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                crate::leanh::lean_inc_ref(v_env_1778_);
                crate::leanh::lean_dec(v___x_1777_);
                v___x_1779_ = l_Lean_Name_isAnonymous(v_declHint_1774_);
                if v___x_1779_ == 0 {
                    v_isExporting_1780_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1778_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1780_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1778_);
                        crate::leanh::lean_dec(v_declHint_1774_);
                        v___x_1781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1781_, 0, v_msg_1773_);
                        return v___x_1781_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1778_);
                        v___x_1782_ = l_Lean_Environment_setExporting(v_env_1778_, v___x_1779_);
                        crate::leanh::lean_inc(v_declHint_1774_);
                        crate::leanh::lean_inc_ref(v___x_1782_);
                        v___x_1783_ = l_Lean_Environment_contains(
                            v___x_1782_,
                            v_declHint_1774_,
                            v_isExporting_1780_,
                        );
                        if v___x_1783_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1782_);
                            crate::leanh::lean_dec_ref(v_env_1778_);
                            crate::leanh::lean_dec(v_declHint_1774_);
                            v___x_1784_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1784_, 0, v_msg_1773_);
                            return v___x_1784_;
                        } else {
                            v___x_1785_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_1786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_1787_ = l_Lean_Options_empty;
                            v___x_1788_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1788_, 0, v___x_1782_);
                            crate::leanh::lean_ctor_set(v___x_1788_, 1, v___x_1785_);
                            crate::leanh::lean_ctor_set(v___x_1788_, 2, v___x_1786_);
                            crate::leanh::lean_ctor_set(v___x_1788_, 3, v___x_1787_);
                            crate::leanh::lean_inc(v_declHint_1774_);
                            v___x_1789_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1774_, v___x_1779_);
                            v_c_1790_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1790_, 0, v___x_1788_);
                            crate::leanh::lean_ctor_set(v_c_1790_, 1, v___x_1789_);
                            v___x_1791_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1778_,
                                v_declHint_1774_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1791_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1778_);
                                crate::leanh::lean_dec(v_declHint_1774_);
                                v___x_1792_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_1793_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                                crate::leanh::lean_ctor_set(v___x_1793_, 1, v_c_1790_);
                                v___x_1794_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_1795_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1793_);
                                crate::leanh::lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                                v___x_1796_ = l_Lean_MessageData_note(v___x_1795_);
                                v___x_1797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1797_, 0, v_msg_1773_);
                                crate::leanh::lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                                v___x_1798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1798_, 0, v___x_1797_);
                                return v___x_1798_;
                            } else {
                                v_val_1799_ = crate::leanh::lean_ctor_get(v___x_1791_, 0);
                                v_isSharedCheck_1834_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1791_)) as u8;
                                if v_isSharedCheck_1834_ == 0 {
                                    v___x_1801_ = v___x_1791_;
                                    v_isShared_1802_ = v_isSharedCheck_1834_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1799_);
                                    crate::leanh::lean_dec(v___x_1791_);
                                    v___x_1801_ = crate::leanh::lean_box(0);
                                    v_isShared_1802_ = v_isSharedCheck_1834_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1778_);
                    crate::leanh::lean_dec(v_declHint_1774_);
                    v___x_1835_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1835_, 0, v_msg_1773_);
                    return v___x_1835_;
                }
            }
            1 => {
                v___x_1803_ = crate::leanh::lean_box(0);
                v___x_1804_ = l_Lean_Environment_header(v_env_1778_);
                crate::leanh::lean_dec_ref(v_env_1778_);
                v___x_1805_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1804_);
                v_mod_1806_ = lean_array_get(v___x_1803_, v___x_1805_, v_val_1799_);
                crate::leanh::lean_dec(v_val_1799_);
                crate::leanh::lean_dec_ref(v___x_1805_);
                v___x_1807_ = l_Lean_isPrivateName(v_declHint_1774_);
                crate::leanh::lean_dec(v_declHint_1774_);
                if v___x_1807_ == 0 {
                    v___x_1808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_1809_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                    crate::leanh::lean_ctor_set(v___x_1809_, 1, v_c_1790_);
                    v___x_1810_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_1811_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1811_, 0, v___x_1809_);
                    crate::leanh::lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                    v___x_1812_ = l_Lean_MessageData_ofName(v_mod_1806_);
                    v___x_1813_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1813_, 0, v___x_1811_);
                    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1812_);
                    v___x_1814_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_1815_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1815_, 0, v___x_1813_);
                    crate::leanh::lean_ctor_set(v___x_1815_, 1, v___x_1814_);
                    v___x_1816_ = l_Lean_MessageData_note(v___x_1815_);
                    v___x_1817_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1817_, 0, v_msg_1773_);
                    crate::leanh::lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                    if v_isShared_1802_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1801_, 0);
                        crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1801_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1821_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_1822_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1822_, 0, v___x_1821_);
                    crate::leanh::lean_ctor_set(v___x_1822_, 1, v_c_1790_);
                    v___x_1823_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_1824_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1824_, 0, v___x_1822_);
                    crate::leanh::lean_ctor_set(v___x_1824_, 1, v___x_1823_);
                    v___x_1825_ = l_Lean_MessageData_ofName(v_mod_1806_);
                    v___x_1826_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1824_);
                    crate::leanh::lean_ctor_set(v___x_1826_, 1, v___x_1825_);
                    v___x_1827_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_1828_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1828_, 0, v___x_1826_);
                    crate::leanh::lean_ctor_set(v___x_1828_, 1, v___x_1827_);
                    v___x_1829_ = l_Lean_MessageData_note(v___x_1828_);
                    v___x_1830_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v_msg_1773_);
                    crate::leanh::lean_ctor_set(v___x_1830_, 1, v___x_1829_);
                    if v_isShared_1802_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1801_, 0);
                        crate::leanh::lean_ctor_set(v___x_1801_, 0, v___x_1830_);
                        v___x_1832_ = v___x_1801_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1833_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
                        v___x_1832_ = v_reuseFailAlloc_1833_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1819_;
            }
            3 => {
                return v___x_1832_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___boxed(
    mut v_msg_1836_: *mut crate::leanh::LeanObject,
    mut v_declHint_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1836_, v_declHint_1837_, v___y_1838_);
    crate::leanh::lean_dec(v___y_1838_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(
    mut v_msg_1841_: *mut crate::leanh::LeanObject,
    mut v_declHint_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1841_, v_declHint_1842_, v___y_1846_);
                v_a_1849_ = crate::leanh::lean_ctor_get(v___x_1848_, 0);
                v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___x_1848_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1851_ = v___x_1848_;
                    v_isShared_1852_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1849_);
                    crate::leanh::lean_dec(v___x_1848_);
                    v___x_1851_ = crate::leanh::lean_box(0);
                    v_isShared_1852_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1853_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1854_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1854_, 0, v___x_1853_);
                crate::leanh::lean_ctor_set(v___x_1854_, 1, v_a_1849_);
                if v_isShared_1852_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1851_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1856_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8___boxed(
    mut v_msg_1859_: *mut crate::leanh::LeanObject,
    mut v_declHint_1860_: *mut crate::leanh::LeanObject,
    mut v___y_1861_: *mut crate::leanh::LeanObject,
    mut v___y_1862_: *mut crate::leanh::LeanObject,
    mut v___y_1863_: *mut crate::leanh::LeanObject,
    mut v___y_1864_: *mut crate::leanh::LeanObject,
    mut v___y_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_1859_, v_declHint_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    crate::leanh::lean_dec(v___y_1864_);
    crate::leanh::lean_dec_ref(v___y_1863_);
    crate::leanh::lean_dec(v___y_1862_);
    crate::leanh::lean_dec_ref(v___y_1861_);
    return v_res_1866_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(
    mut v_ref_1867_: *mut crate::leanh::LeanObject,
    mut v_msg_1868_: *mut crate::leanh::LeanObject,
    mut v_declHint_1869_: *mut crate::leanh::LeanObject,
    mut v___y_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
    mut v___y_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_1868_, v_declHint_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
    v_a_1876_ = crate::leanh::lean_ctor_get(v___x_1875_, 0);
    crate::leanh::lean_inc(v_a_1876_);
    crate::leanh::lean_dec_ref(v___x_1875_);
    v___x_1877_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_1867_, v_a_1876_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
    return v___x_1877_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(
    mut v_ref_1878_: *mut crate::leanh::LeanObject,
    mut v_msg_1879_: *mut crate::leanh::LeanObject,
    mut v_declHint_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
    mut v___y_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1878_, v_msg_1879_, v_declHint_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    crate::leanh::lean_dec(v___y_1884_);
    crate::leanh::lean_dec_ref(v___y_1883_);
    crate::leanh::lean_dec(v___y_1882_);
    crate::leanh::lean_dec_ref(v___y_1881_);
    crate::leanh::lean_dec(v_ref_1878_);
    return v_res_1886_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0;
    v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2;
    v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_ref_1893_: *mut crate::leanh::LeanObject,
    mut v_constName_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v___y_1896_: *mut crate::leanh::LeanObject,
    mut v___y_1897_: *mut crate::leanh::LeanObject,
    mut v___y_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
    v___x_1901_ = 0;
    crate::leanh::lean_inc(v_constName_1894_);
    v___x_1902_ = l_Lean_MessageData_ofConstName(v_constName_1894_, v___x_1901_);
    v___x_1903_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1900_);
    crate::leanh::lean_ctor_set(v___x_1903_, 1, v___x_1902_);
    v___x_1904_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
    v___x_1905_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1905_, 0, v___x_1903_);
    crate::leanh::lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    v___x_1906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1893_, v___x_1905_, v_constName_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_ref_1907_: *mut crate::leanh::LeanObject,
    mut v_constName_1908_: *mut crate::leanh::LeanObject,
    mut v___y_1909_: *mut crate::leanh::LeanObject,
    mut v___y_1910_: *mut crate::leanh::LeanObject,
    mut v___y_1911_: *mut crate::leanh::LeanObject,
    mut v___y_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1907_, v_constName_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    crate::leanh::lean_dec(v___y_1912_);
    crate::leanh::lean_dec_ref(v___y_1911_);
    crate::leanh::lean_dec(v___y_1910_);
    crate::leanh::lean_dec_ref(v___y_1909_);
    crate::leanh::lean_dec(v_ref_1907_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(
    mut v_constName_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1921_ = crate::leanh::lean_ctor_get(v___y_1918_, 5);
    v___x_1922_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1921_, v_constName_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
    crate::leanh::lean_dec(v___y_1927_);
    crate::leanh::lean_dec_ref(v___y_1926_);
    crate::leanh::lean_dec(v___y_1925_);
    crate::leanh::lean_dec_ref(v___y_1924_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(
    mut v_constName_1930_: *mut crate::leanh::LeanObject,
    mut v___y_1931_: *mut crate::leanh::LeanObject,
    mut v___y_1932_: *mut crate::leanh::LeanObject,
    mut v___y_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1936_ = lean_st_ref_get(v___y_1934_);
                v_env_1937_ = crate::leanh::lean_ctor_get(v___x_1936_, 0);
                crate::leanh::lean_inc_ref(v_env_1937_);
                crate::leanh::lean_dec(v___x_1936_);
                v___x_1938_ = 0;
                crate::leanh::lean_inc(v_constName_1930_);
                v___x_1939_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_1937_,
                    v_constName_1930_,
                    v___x_1938_,
                );
                if crate::leanh::lean_obj_tag(v___x_1939_) == 0 {
                    v___x_1940_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
                    return v___x_1940_;
                } else {
                    crate::leanh::lean_dec(v_constName_1930_);
                    v_val_1941_ = crate::leanh::lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v___x_1943_ = v___x_1939_;
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1941_);
                        crate::leanh::lean_dec(v___x_1939_);
                        v___x_1943_ = crate::leanh::lean_box(0);
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1943_, 0);
                    v___x_1946_ = v___x_1943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_val_1941_);
                    v___x_1946_ = v_reuseFailAlloc_1947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0___boxed(
    mut v_constName_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
    crate::leanh::lean_dec(v___y_1953_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    crate::leanh::lean_dec(v___y_1951_);
    crate::leanh::lean_dec_ref(v___y_1950_);
    return v_res_1955_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(
    mut v_a_1956_: *mut crate::leanh::LeanObject,
    mut v_a_1957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1956_) == 0 {
                    v___x_1958_ = l_List_reverse___redArg(v_a_1957_);
                    return v___x_1958_;
                } else {
                    v_head_1959_ = crate::leanh::lean_ctor_get(v_a_1956_, 0);
                    v_tail_1960_ = crate::leanh::lean_ctor_get(v_a_1956_, 1);
                    v_isSharedCheck_1969_ = (!crate::leanh::lean_is_exclusive(v_a_1956_)) as u8;
                    if v_isSharedCheck_1969_ == 0 {
                        v___x_1962_ = v_a_1956_;
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1960_);
                        crate::leanh::lean_inc(v_head_1959_);
                        crate::leanh::lean_dec(v_a_1956_);
                        v___x_1962_ = crate::leanh::lean_box(0);
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1964_ = l_Lean_mkLevelParam(v_head_1959_);
                if v_isShared_1963_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1962_, 1, v_a_1957_);
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v___x_1964_);
                    v___x_1966_ = v___x_1962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1968_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1957_);
                    v___x_1966_ = v_reuseFailAlloc_1968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1956_ = v_tail_1960_;
                v_a_1957_ = v___x_1966_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(
    mut v_constName_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1980_: u8 = 0;
    let mut v_levelParams_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_constName_1970_);
                v___x_1976_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
                if crate::leanh::lean_obj_tag(v___x_1976_) == 0 {
                    v_a_1977_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1988_ = (!crate::leanh::lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1979_ = v___x_1976_;
                        v_isShared_1980_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1977_);
                        crate::leanh::lean_dec(v___x_1976_);
                        v___x_1979_ = crate::leanh::lean_box(0);
                        v_isShared_1980_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_constName_1970_);
                    v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1996_ = (!crate::leanh::lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1996_ == 0 {
                        v___x_1991_ = v___x_1976_;
                        v_isShared_1992_ = v_isSharedCheck_1996_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1989_);
                        crate::leanh::lean_dec(v___x_1976_);
                        v___x_1991_ = crate::leanh::lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_1996_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_1981_ = crate::leanh::lean_ctor_get(v_a_1977_, 1);
                crate::leanh::lean_inc(v_levelParams_1981_);
                crate::leanh::lean_dec(v_a_1977_);
                v___x_1982_ = crate::leanh::lean_box(0);
                v___x_1983_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(v_levelParams_1981_, v___x_1982_);
                v___x_1984_ = l_Lean_mkConst(v_constName_1970_, v___x_1983_);
                if v_isShared_1980_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1979_, 0, v___x_1984_);
                    v___x_1986_ = v___x_1979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1986_;
            }
            3 => {
                if v_isShared_1992_ == 0 {
                    v___x_1994_ = v___x_1991_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1995_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
                    v___x_1994_ = v_reuseFailAlloc_1995_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1994_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0___boxed(
    mut v_constName_1997_: *mut crate::leanh::LeanObject,
    mut v___y_1998_: *mut crate::leanh::LeanObject,
    mut v___y_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2003_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(
        v_constName_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
        v___y_2001_,
    );
    crate::leanh::lean_dec(v___y_2001_);
    crate::leanh::lean_dec_ref(v___y_2000_);
    crate::leanh::lean_dec(v___y_1999_);
    crate::leanh::lean_dec_ref(v___y_1998_);
    return v_res_2003_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(
    mut v_as_2004_: *mut crate::leanh::LeanObject,
    mut v_j_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2010_: u8 = 0;
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = lean_array_get_size(v_as_2004_);
                v___x_2007_ = lean_nat_dec_lt(v_j_2005_, v___x_2006_);
                if v___x_2007_ == 0 {
                    crate::leanh::lean_dec(v_j_2005_);
                    v___x_2008_ = crate::leanh::lean_box(0);
                    return v___x_2008_;
                } else {
                    v___x_2009_ = lean_array_fget_borrowed(v_as_2004_, v_j_2005_);
                    v_binderInfo_2010_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_2009_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_2011_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2010_);
                    if v___x_2011_ == 0 {
                        v___x_2012_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2013_ = lean_nat_add(v_j_2005_, v___x_2012_);
                        crate::leanh::lean_dec(v_j_2005_);
                        v_j_2005_ = v___x_2013_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2015_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2015_, 0, v_j_2005_);
                        return v___x_2015_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1___boxed(
    mut v_as_2016_: *mut crate::leanh::LeanObject,
    mut v_j_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ =
        l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_as_2016_, v_j_2017_);
    crate::leanh::lean_dec_ref(v_as_2016_);
    return v_res_2018_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2019_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2019_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__0_once),
        _init_l_Lean_Meta_registerCoercion___closed__0,
    );
    v___x_2021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2021_, 0, v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2022_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1_once),
        _init_l_Lean_Meta_registerCoercion___closed__1,
    );
    v___x_2023_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    crate::leanh::lean_ctor_set(v___x_2023_, 1, v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1_once),
        _init_l_Lean_Meta_registerCoercion___closed__1,
    );
    v___x_2025_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 1, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 2, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 3, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 4, v___x_2024_);
    crate::leanh::lean_ctor_set(v___x_2025_, 5, v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = l_Lean_Meta_registerCoercion___closed__4;
    v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_Meta_registerCoercion(
    mut v_name_2029_: *mut crate::leanh::LeanObject,
    mut v_info_2030_: *mut crate::leanh::LeanObject,
    mut v_a_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_a_2033_: *mut crate::leanh::LeanObject,
    mut v_a_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_info_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_unused_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut v_reuseFailAlloc_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_val_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_info_2030_) == 0 {
                    crate::leanh::lean_inc(v_name_2029_);
                    v___x_2079_ =
                        l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(
                            v_name_2029_,
                            v_a_2031_,
                            v_a_2032_,
                            v_a_2033_,
                            v_a_2034_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2079_) == 0 {
                        v_a_2080_ = crate::leanh::lean_ctor_get(v___x_2079_, 0);
                        crate::leanh::lean_inc(v_a_2080_);
                        crate::leanh::lean_dec_ref_known(v___x_2079_, 1);
                        v___x_2081_ = crate::leanh::lean_box(0);
                        v___x_2082_ = l_Lean_Meta_getFunInfo(
                            v_a_2080_,
                            v___x_2081_,
                            v_a_2031_,
                            v_a_2032_,
                            v_a_2033_,
                            v_a_2034_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2082_) == 0 {
                            v_a_2083_ = crate::leanh::lean_ctor_get(v___x_2082_, 0);
                            crate::leanh::lean_inc(v_a_2083_);
                            crate::leanh::lean_dec_ref_known(v___x_2082_, 1);
                            v_paramInfo_2084_ = crate::leanh::lean_ctor_get(v_a_2083_, 0);
                            v_isSharedCheck_2109_ =
                                (!crate::leanh::lean_is_exclusive(v_a_2083_)) as u8;
                            if v_isSharedCheck_2109_ == 0 {
                                v_unused_2110_ = crate::leanh::lean_ctor_get(v_a_2083_, 1);
                                crate::leanh::lean_dec(v_unused_2110_);
                                v___x_2086_ = v_a_2083_;
                                v_isShared_2087_ = v_isSharedCheck_2109_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_paramInfo_2084_);
                                crate::leanh::lean_dec(v_a_2083_);
                                v___x_2086_ = crate::leanh::lean_box(0);
                                v_isShared_2087_ = v_isSharedCheck_2109_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_name_2029_);
                            v_a_2111_ = crate::leanh::lean_ctor_get(v___x_2082_, 0);
                            v_isSharedCheck_2118_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2082_)) as u8;
                            if v_isSharedCheck_2118_ == 0 {
                                v___x_2113_ = v___x_2082_;
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2111_);
                                crate::leanh::lean_dec(v___x_2082_);
                                v___x_2113_ = crate::leanh::lean_box(0);
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_name_2029_);
                        v_a_2119_ = crate::leanh::lean_ctor_get(v___x_2079_, 0);
                        v_isSharedCheck_2126_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2079_)) as u8;
                        if v_isSharedCheck_2126_ == 0 {
                            v___x_2121_ = v___x_2079_;
                            v_isShared_2122_ = v_isSharedCheck_2126_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2119_);
                            crate::leanh::lean_dec(v___x_2079_);
                            v___x_2121_ = crate::leanh::lean_box(0);
                            v_isShared_2122_ = v_isSharedCheck_2126_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v_val_2127_ = crate::leanh::lean_ctor_get(v_info_2030_, 0);
                    crate::leanh::lean_inc(v_val_2127_);
                    crate::leanh::lean_dec_ref_known(v_info_2030_, 1);
                    v_info_2037_ = v_val_2127_;
                    v___y_2038_ = v_a_2032_;
                    v___y_2039_ = v_a_2034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2040_ = lean_st_ref_take(v___y_2039_);
                v_env_2041_ = crate::leanh::lean_ctor_get(v___x_2040_, 0);
                v_nextMacroScope_2042_ = crate::leanh::lean_ctor_get(v___x_2040_, 1);
                v_ngen_2043_ = crate::leanh::lean_ctor_get(v___x_2040_, 2);
                v_auxDeclNGen_2044_ = crate::leanh::lean_ctor_get(v___x_2040_, 3);
                v_traceState_2045_ = crate::leanh::lean_ctor_get(v___x_2040_, 4);
                v_messages_2046_ = crate::leanh::lean_ctor_get(v___x_2040_, 6);
                v_infoState_2047_ = crate::leanh::lean_ctor_get(v___x_2040_, 7);
                v_snapshotTasks_2048_ = crate::leanh::lean_ctor_get(v___x_2040_, 8);
                v_isSharedCheck_2077_ = (!crate::leanh::lean_is_exclusive(v___x_2040_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = crate::leanh::lean_ctor_get(v___x_2040_, 5);
                    crate::leanh::lean_dec(v_unused_2078_);
                    v___x_2050_ = v___x_2040_;
                    v_isShared_2051_ = v_isSharedCheck_2077_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2048_);
                    crate::leanh::lean_inc(v_infoState_2047_);
                    crate::leanh::lean_inc(v_messages_2046_);
                    crate::leanh::lean_inc(v_traceState_2045_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2044_);
                    crate::leanh::lean_inc(v_ngen_2043_);
                    crate::leanh::lean_inc(v_nextMacroScope_2042_);
                    crate::leanh::lean_inc(v_env_2041_);
                    crate::leanh::lean_dec(v___x_2040_);
                    v___x_2050_ = crate::leanh::lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2052_ = l_Lean_Meta_coeExt;
                v___x_2053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2053_, 0, v_name_2029_);
                crate::leanh::lean_ctor_set(v___x_2053_, 1, v_info_2037_);
                v___x_2054_ = l_Lean_ScopedEnvExtension_addEntry___redArg(
                    v___x_2052_,
                    v_env_2041_,
                    v___x_2053_,
                );
                v___x_2055_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__2_once),
                    _init_l_Lean_Meta_registerCoercion___closed__2,
                );
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 5, v___x_2055_);
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v___x_2054_);
                    v___x_2057_ = v___x_2050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_nextMacroScope_2042_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_ngen_2043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_auxDeclNGen_2044_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_traceState_2045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 5, v___x_2055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_messages_2046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_infoState_2047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2076_, 8, v_snapshotTasks_2048_);
                    v___x_2057_ = v_reuseFailAlloc_2076_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2058_ = lean_st_ref_set(v___y_2039_, v___x_2057_);
                v___x_2059_ = lean_st_ref_take(v___y_2038_);
                v_mctx_2060_ = crate::leanh::lean_ctor_get(v___x_2059_, 0);
                v_zetaDeltaFVarIds_2061_ = crate::leanh::lean_ctor_get(v___x_2059_, 2);
                v_postponed_2062_ = crate::leanh::lean_ctor_get(v___x_2059_, 3);
                v_diag_2063_ = crate::leanh::lean_ctor_get(v___x_2059_, 4);
                v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_2059_)) as u8;
                if v_isSharedCheck_2074_ == 0 {
                    v_unused_2075_ = crate::leanh::lean_ctor_get(v___x_2059_, 1);
                    crate::leanh::lean_dec(v_unused_2075_);
                    v___x_2065_ = v___x_2059_;
                    v_isShared_2066_ = v_isSharedCheck_2074_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2063_);
                    crate::leanh::lean_inc(v_postponed_2062_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2061_);
                    crate::leanh::lean_inc(v_mctx_2060_);
                    crate::leanh::lean_dec(v___x_2059_);
                    v___x_2065_ = crate::leanh::lean_box(0);
                    v_isShared_2066_ = v_isSharedCheck_2074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2067_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__3_once),
                    _init_l_Lean_Meta_registerCoercion___closed__3,
                );
                if v_isShared_2066_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2065_, 1, v___x_2067_);
                    v___x_2069_ = v___x_2065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_mctx_2060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2067_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2073_,
                        2,
                        v_zetaDeltaFVarIds_2061_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_postponed_2062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_diag_2063_);
                    v___x_2069_ = v_reuseFailAlloc_2073_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2070_ = lean_st_ref_set(v___y_2038_, v___x_2069_);
                v___x_2071_ = crate::leanh::lean_box(0);
                v___x_2072_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                return v___x_2072_;
            }
            6 => {
                v___x_2088_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2089_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(
                    v_paramInfo_2084_,
                    v___x_2088_,
                );
                crate::leanh::lean_dec_ref(v_paramInfo_2084_);
                if crate::leanh::lean_obj_tag(v___x_2089_) == 1 {
                    crate::leanh::lean_del_object(v___x_2086_);
                    v_val_2090_ = crate::leanh::lean_ctor_get(v___x_2089_, 0);
                    crate::leanh::lean_inc(v_val_2090_);
                    crate::leanh::lean_dec_ref_known(v___x_2089_, 1);
                    v___x_2091_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2092_ = lean_nat_add(v_val_2090_, v___x_2091_);
                    v___x_2093_ = 0;
                    v___x_2094_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2094_, 0, v___x_2092_);
                    crate::leanh::lean_ctor_set(v___x_2094_, 1, v_val_2090_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2094_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v___x_2093_,
                    );
                    v_info_2037_ = v___x_2094_;
                    v___y_2038_ = v_a_2032_;
                    v___y_2039_ = v_a_2034_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2089_);
                    v___x_2095_ = l_Lean_MessageData_ofName(v_name_2029_);
                    v___x_2096_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__5_once),
                        _init_l_Lean_Meta_registerCoercion___closed__5,
                    );
                    if v_isShared_2087_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2086_, 7);
                        crate::leanh::lean_ctor_set(v___x_2086_, 1, v___x_2096_);
                        crate::leanh::lean_ctor_set(v___x_2086_, 0, v___x_2095_);
                        v___x_2098_ = v___x_2086_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2108_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2095_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2096_);
                        v___x_2098_ = v_reuseFailAlloc_2108_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                v___x_2099_ =
                    l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
                        v___x_2098_,
                        v_a_2031_,
                        v_a_2032_,
                        v_a_2033_,
                        v_a_2034_,
                    );
                v_a_2100_ = crate::leanh::lean_ctor_get(v___x_2099_, 0);
                v_isSharedCheck_2107_ = (!crate::leanh::lean_is_exclusive(v___x_2099_)) as u8;
                if v_isSharedCheck_2107_ == 0 {
                    v___x_2102_ = v___x_2099_;
                    v_isShared_2103_ = v_isSharedCheck_2107_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2100_);
                    crate::leanh::lean_dec(v___x_2099_);
                    v___x_2102_ = crate::leanh::lean_box(0);
                    v_isShared_2103_ = v_isSharedCheck_2107_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2103_ == 0 {
                    v___x_2105_ = v___x_2102_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
                    v___x_2105_ = v_reuseFailAlloc_2106_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2105_;
            }
            10 => {
                if v_isShared_2114_ == 0 {
                    v___x_2116_ = v___x_2113_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2116_;
            }
            12 => {
                if v_isShared_2122_ == 0 {
                    v___x_2124_ = v___x_2121_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
                    v___x_2124_ = v_reuseFailAlloc_2125_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2124_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_registerCoercion___boxed(
    mut v_name_2128_: *mut crate::leanh::LeanObject,
    mut v_info_2129_: *mut crate::leanh::LeanObject,
    mut v_a_2130_: *mut crate::leanh::LeanObject,
    mut v_a_2131_: *mut crate::leanh::LeanObject,
    mut v_a_2132_: *mut crate::leanh::LeanObject,
    mut v_a_2133_: *mut crate::leanh::LeanObject,
    mut v_a_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2135_ = l_Lean_Meta_registerCoercion(
        v_name_2128_,
        v_info_2129_,
        v_a_2130_,
        v_a_2131_,
        v_a_2132_,
        v_a_2133_,
    );
    crate::leanh::lean_dec(v_a_2133_);
    crate::leanh::lean_dec_ref(v_a_2132_);
    crate::leanh::lean_dec(v_a_2131_);
    crate::leanh::lean_dec_ref(v_a_2130_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(
    mut v_00_u03b1_2136_: *mut crate::leanh::LeanObject,
    mut v_msg_2137_: *mut crate::leanh::LeanObject,
    mut v___y_2138_: *mut crate::leanh::LeanObject,
    mut v___y_2139_: *mut crate::leanh::LeanObject,
    mut v___y_2140_: *mut crate::leanh::LeanObject,
    mut v___y_2141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
        v_msg_2137_,
        v___y_2138_,
        v___y_2139_,
        v___y_2140_,
        v___y_2141_,
    );
    return v___x_2143_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___boxed(
    mut v_00_u03b1_2144_: *mut crate::leanh::LeanObject,
    mut v_msg_2145_: *mut crate::leanh::LeanObject,
    mut v___y_2146_: *mut crate::leanh::LeanObject,
    mut v___y_2147_: *mut crate::leanh::LeanObject,
    mut v___y_2148_: *mut crate::leanh::LeanObject,
    mut v___y_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(
        v_00_u03b1_2144_,
        v_msg_2145_,
        v___y_2146_,
        v___y_2147_,
        v___y_2148_,
        v___y_2149_,
    );
    crate::leanh::lean_dec(v___y_2149_);
    crate::leanh::lean_dec_ref(v___y_2148_);
    crate::leanh::lean_dec(v___y_2147_);
    crate::leanh::lean_dec_ref(v___y_2146_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2152_: *mut crate::leanh::LeanObject,
    mut v_constName_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
    mut v___y_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2160_: *mut crate::leanh::LeanObject,
    mut v_constName_2161_: *mut crate::leanh::LeanObject,
    mut v___y_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
    mut v___y_2165_: *mut crate::leanh::LeanObject,
    mut v___y_2166_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(v_00_u03b1_2160_, v_constName_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
    crate::leanh::lean_dec(v___y_2165_);
    crate::leanh::lean_dec_ref(v___y_2164_);
    crate::leanh::lean_dec(v___y_2163_);
    crate::leanh::lean_dec_ref(v___y_2162_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b1_2168_: *mut crate::leanh::LeanObject,
    mut v_ref_2169_: *mut crate::leanh::LeanObject,
    mut v_constName_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
    mut v___y_2174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2176_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_2169_, v_constName_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
    return v___x_2176_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b1_2177_: *mut crate::leanh::LeanObject,
    mut v_ref_2178_: *mut crate::leanh::LeanObject,
    mut v_constName_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
    mut v___y_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_2177_, v_ref_2178_, v_constName_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    crate::leanh::lean_dec(v___y_2183_);
    crate::leanh::lean_dec_ref(v___y_2182_);
    crate::leanh::lean_dec(v___y_2181_);
    crate::leanh::lean_dec_ref(v___y_2180_);
    crate::leanh::lean_dec(v_ref_2178_);
    return v_res_2185_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(
    mut v_00_u03b1_2186_: *mut crate::leanh::LeanObject,
    mut v_ref_2187_: *mut crate::leanh::LeanObject,
    mut v_msg_2188_: *mut crate::leanh::LeanObject,
    mut v_declHint_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
    mut v___y_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_2187_, v_msg_2188_, v_declHint_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(
    mut v_00_u03b1_2196_: *mut crate::leanh::LeanObject,
    mut v_ref_2197_: *mut crate::leanh::LeanObject,
    mut v_msg_2198_: *mut crate::leanh::LeanObject,
    mut v_declHint_2199_: *mut crate::leanh::LeanObject,
    mut v___y_2200_: *mut crate::leanh::LeanObject,
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
    mut v___y_2203_: *mut crate::leanh::LeanObject,
    mut v___y_2204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_2196_, v_ref_2197_, v_msg_2198_, v_declHint_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
    crate::leanh::lean_dec(v___y_2203_);
    crate::leanh::lean_dec_ref(v___y_2202_);
    crate::leanh::lean_dec(v___y_2201_);
    crate::leanh::lean_dec_ref(v___y_2200_);
    crate::leanh::lean_dec(v_ref_2197_);
    return v_res_2205_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_2206_: *mut crate::leanh::LeanObject,
    mut v_declHint_2207_: *mut crate::leanh::LeanObject,
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
    mut v___y_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2213_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2206_, v_declHint_2207_, v___y_2211_);
    return v___x_2213_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_2214_: *mut crate::leanh::LeanObject,
    mut v_declHint_2215_: *mut crate::leanh::LeanObject,
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v___y_2217_: *mut crate::leanh::LeanObject,
    mut v___y_2218_: *mut crate::leanh::LeanObject,
    mut v___y_2219_: *mut crate::leanh::LeanObject,
    mut v___y_2220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(v_msg_2214_, v_declHint_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
    crate::leanh::lean_dec(v___y_2219_);
    crate::leanh::lean_dec_ref(v___y_2218_);
    crate::leanh::lean_dec(v___y_2217_);
    crate::leanh::lean_dec_ref(v___y_2216_);
    return v_res_2221_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(
    mut v_00_u03b1_2222_: *mut crate::leanh::LeanObject,
    mut v_ref_2223_: *mut crate::leanh::LeanObject,
    mut v_msg_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
    mut v___y_2228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_2223_, v_msg_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
    return v___x_2230_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_2231_: *mut crate::leanh::LeanObject,
    mut v_ref_2232_: *mut crate::leanh::LeanObject,
    mut v_msg_2233_: *mut crate::leanh::LeanObject,
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
    mut v___y_2237_: *mut crate::leanh::LeanObject,
    mut v___y_2238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_2231_, v_ref_2232_, v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
    crate::leanh::lean_dec(v___y_2237_);
    crate::leanh::lean_dec_ref(v___y_2236_);
    crate::leanh::lean_dec(v___y_2235_);
    crate::leanh::lean_dec_ref(v___y_2234_);
    crate::leanh::lean_dec(v_ref_2232_);
    return v_res_2239_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v_decl_2240_: *mut crate::leanh::LeanObject,
    mut v_____r_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2247_ = crate::leanh::lean_box(0);
    v___x_2248_ = l_Lean_Meta_registerCoercion(
        v_decl_2240_,
        v___x_2247_,
        v___y_2242_,
        v___y_2243_,
        v___y_2244_,
        v___y_2245_,
    );
    return v___x_2248_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v_decl_2249_: *mut crate::leanh::LeanObject,
    mut v_____r_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_2249_, v_____r_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
    crate::leanh::lean_dec(v___y_2254_);
    crate::leanh::lean_dec_ref(v___y_2253_);
    crate::leanh::lean_dec(v___y_2252_);
    crate::leanh::lean_dec_ref(v___y_2251_);
    return v_res_2256_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2258_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2261_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_2266_: *mut crate::leanh::LeanObject,
    mut v_kind_2267_: u8,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_2274_ = l_Lean_MessageData_ofName(v_name_2266_);
                v___x_2275_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2275_, 0, v___x_2273_);
                crate::leanh::lean_ctor_set(v___x_2275_, 1, v___x_2274_);
                v___x_2276_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_2277_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2275_);
                crate::leanh::lean_ctor_set(v___x_2277_, 1, v___x_2276_);
                match v_kind_2267_ {
                    0 => {
                        v___x_2286_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4;
                        v___y_2279_ = v___x_2286_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2287_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5;
                        v___y_2279_ = v___x_2287_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2288_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6;
                        v___y_2279_ = v___x_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2279_);
                v___x_2280_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2280_, 0, v___y_2279_);
                v___x_2281_ = l_Lean_MessageData_ofFormat(v___x_2280_);
                v___x_2282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2282_, 0, v___x_2277_);
                crate::leanh::lean_ctor_set(v___x_2282_, 1, v___x_2281_);
                v___x_2283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
                v___x_2284_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2284_, 0, v___x_2282_);
                crate::leanh::lean_ctor_set(v___x_2284_, 1, v___x_2283_);
                v___x_2285_ =
                    l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
                        v___x_2284_,
                        v___y_2268_,
                        v___y_2269_,
                        v___y_2270_,
                        v___y_2271_,
                    );
                return v___x_2285_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_name_2289_: *mut crate::leanh::LeanObject,
    mut v_kind_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
    mut v___y_2293_: *mut crate::leanh::LeanObject,
    mut v___y_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2296_ = (crate::leanh::lean_unbox(v_kind_2290_) as u8);
    v_res_2297_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_2289_, v_kind_boxed_2296_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
    crate::leanh::lean_dec(v___y_2294_);
    crate::leanh::lean_dec_ref(v___y_2293_);
    crate::leanh::lean_dec(v___y_2292_);
    crate::leanh::lean_dec_ref(v___y_2291_);
    return v_res_2297_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u64 = 0;
    v___x_2304_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2306_: u64 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2306_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2307_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2308_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_2308_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_2306_,
    );
    return v___x_2308_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2309_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2313_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2313_, 0, v___x_2312_);
    crate::leanh::lean_ctor_set(v___x_2313_, 1, v___x_2312_);
    crate::leanh::lean_ctor_set(v___x_2313_, 2, v___x_2312_);
    crate::leanh::lean_ctor_set(v___x_2313_, 3, v___x_2312_);
    crate::leanh::lean_ctor_set(v___x_2313_, 4, v___x_2312_);
    crate::leanh::lean_ctor_set(v___x_2313_, 5, v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2315_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    crate::leanh::lean_ctor_set(v___x_2315_, 1, v___x_2314_);
    crate::leanh::lean_ctor_set(v___x_2315_, 2, v___x_2314_);
    crate::leanh::lean_ctor_set(v___x_2315_, 3, v___x_2314_);
    crate::leanh::lean_ctor_set(v___x_2315_, 4, v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v___x_2316_: *mut crate::leanh::LeanObject,
    mut v___x_2317_: *mut crate::leanh::LeanObject,
    mut v___x_2318_: *mut crate::leanh::LeanObject,
    mut v_decl_2319_: *mut crate::leanh::LeanObject,
    mut v___stx_2320_: *mut crate::leanh::LeanObject,
    mut v_kind_2321_: u8,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2325_ = 1;
                v___x_2326_ = 0;
                v___x_2327_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2328_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2329_ = crate::leanh::lean_unsigned_to_nat(32);
                v___x_2330_ = lean_mk_empty_array_with_capacity(v___x_2329_);
                v___x_2331_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
                v___x_2332_ = 5usize;
                crate::leanh::lean_inc_n(v___x_2316_, 6);
                v___x_2333_ =
                    crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2331_);
                crate::leanh::lean_ctor_set(v___x_2333_, 1, v___x_2330_);
                crate::leanh::lean_ctor_set(v___x_2333_, 2, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2333_, 3, v___x_2316_);
                crate::leanh::lean_ctor_set_usize(v___x_2333_, 4, v___x_2332_);
                v___x_2334_ = crate::leanh::lean_box(1);
                crate::leanh::lean_inc_ref(v___x_2333_);
                v___x_2335_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2335_, 1, v___x_2333_);
                crate::leanh::lean_ctor_set(v___x_2335_, 2, v___x_2334_);
                v___x_2336_ = lean_mk_empty_array_with_capacity(v___x_2316_);
                v___x_2337_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_2317_);
                v___x_2338_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2338_, 0, v___x_2327_);
                crate::leanh::lean_ctor_set(v___x_2338_, 1, v___x_2317_);
                crate::leanh::lean_ctor_set(v___x_2338_, 2, v___x_2335_);
                crate::leanh::lean_ctor_set(v___x_2338_, 3, v___x_2336_);
                crate::leanh::lean_ctor_set(v___x_2338_, 4, v___x_2337_);
                crate::leanh::lean_ctor_set(v___x_2338_, 5, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2338_, 6, v___x_2337_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_2326_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_2326_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_2326_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_2325_,
                );
                v___x_2339_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2339_, 0, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2339_, 1, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2339_, 2, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2339_, 3, v___x_2316_);
                crate::leanh::lean_ctor_set(v___x_2339_, 4, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2339_, 5, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2339_, 6, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2339_, 7, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2339_, 8, v___x_2328_);
                crate::leanh::lean_ctor_set(v___x_2339_, 9, v___x_2328_);
                v___x_2340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2341_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2342_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2342_, 0, v___x_2339_);
                crate::leanh::lean_ctor_set(v___x_2342_, 1, v___x_2340_);
                crate::leanh::lean_ctor_set(v___x_2342_, 2, v___x_2317_);
                crate::leanh::lean_ctor_set(v___x_2342_, 3, v___x_2333_);
                crate::leanh::lean_ctor_set(v___x_2342_, 4, v___x_2341_);
                v___x_2343_ = lean_st_mk_ref(v___x_2342_);
                v___x_2355_ = 0;
                v___x_2356_ = l_Lean_instBEqAttributeKind_beq(v_kind_2321_, v___x_2355_);
                if v___x_2356_ == 0 {
                    crate::leanh::lean_dec(v_decl_2319_);
                    v___x_2357_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v___x_2318_, v_kind_2321_, v___x_2338_, v___x_2343_, v___y_2322_, v___y_2323_);
                    crate::leanh::lean_dec_ref_known(v___x_2338_, 7);
                    v___y_2345_ = v___x_2357_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2318_);
                    v___x_2358_ = crate::leanh::lean_box(0);
                    v___x_2359_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_2319_, v___x_2358_, v___x_2338_, v___x_2343_, v___y_2322_, v___y_2323_);
                    crate::leanh::lean_dec_ref_known(v___x_2338_, 7);
                    v___y_2345_ = v___x_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_2345_) == 0 {
                    v_a_2346_ = crate::leanh::lean_ctor_get(v___y_2345_, 0);
                    v_isSharedCheck_2354_ = (!crate::leanh::lean_is_exclusive(v___y_2345_)) as u8;
                    if v_isSharedCheck_2354_ == 0 {
                        v___x_2348_ = v___y_2345_;
                        v_isShared_2349_ = v_isSharedCheck_2354_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2346_);
                        crate::leanh::lean_dec(v___y_2345_);
                        v___x_2348_ = crate::leanh::lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2354_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2343_);
                    return v___y_2345_;
                }
            }
            2 => {
                v___x_2350_ = lean_st_ref_get(v___x_2343_);
                crate::leanh::lean_dec(v___x_2343_);
                crate::leanh::lean_dec(v___x_2350_);
                if v_isShared_2349_ == 0 {
                    v___x_2352_ = v___x_2348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2353_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2346_);
                    v___x_2352_ = v_reuseFailAlloc_2353_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v___x_2360_: *mut crate::leanh::LeanObject,
    mut v___x_2361_: *mut crate::leanh::LeanObject,
    mut v___x_2362_: *mut crate::leanh::LeanObject,
    mut v_decl_2363_: *mut crate::leanh::LeanObject,
    mut v___stx_2364_: *mut crate::leanh::LeanObject,
    mut v_kind_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2369_: u8 = 0;
    let mut v_res_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2369_ = (crate::leanh::lean_unbox(v_kind_2365_) as u8);
    v_res_2370_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_2360_, v___x_2361_, v___x_2362_, v_decl_2363_, v___stx_2364_, v_kind_boxed_2369_, v___y_2366_, v___y_2367_);
    crate::leanh::lean_dec(v___y_2367_);
    crate::leanh::lean_dec_ref(v___y_2366_);
    crate::leanh::lean_dec(v___stx_2364_);
    return v_res_2370_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_st_ref_get(v___y_2373_);
    v_env_2376_ = crate::leanh::lean_ctor_get(v___x_2375_, 0);
    crate::leanh::lean_inc_ref(v_env_2376_);
    crate::leanh::lean_dec(v___x_2375_);
    v_options_2377_ = crate::leanh::lean_ctor_get(v___y_2372_, 2);
    v___x_2378_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
    v___x_2379_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2379_);
    crate::leanh::lean_dec_ref(v___x_2380_);
    v___x_2381_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_2377_);
    v___x_2382_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2382_, 0, v_env_2376_);
    crate::leanh::lean_ctor_set(v___x_2382_, 1, v___x_2378_);
    crate::leanh::lean_ctor_set(v___x_2382_, 2, v___x_2381_);
    crate::leanh::lean_ctor_set(v___x_2382_, 3, v_options_2377_);
    v___x_2383_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    crate::leanh::lean_ctor_set(v___x_2383_, 1, v_msgData_2371_);
    v___x_2384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2384_, 0, v___x_2383_);
    return v___x_2384_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2385_, v___y_2386_, v___y_2387_);
    crate::leanh::lean_dec(v___y_2387_);
    crate::leanh::lean_dec_ref(v___y_2386_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2394_ = crate::leanh::lean_ctor_get(v___y_2391_, 5);
                v___x_2395_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msg_2390_, v___y_2391_, v___y_2392_);
                v_a_2396_ = crate::leanh::lean_ctor_get(v___x_2395_, 0);
                v_isSharedCheck_2404_ = (!crate::leanh::lean_is_exclusive(v___x_2395_)) as u8;
                if v_isSharedCheck_2404_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    v_isShared_2399_ = v_isSharedCheck_2404_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2396_);
                    crate::leanh::lean_dec(v___x_2395_);
                    v___x_2398_ = crate::leanh::lean_box(0);
                    v_isShared_2399_ = v_isSharedCheck_2404_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2394_);
                v___x_2400_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2400_, 0, v_ref_2394_);
                crate::leanh::lean_ctor_set(v___x_2400_, 1, v_a_2396_);
                if v_isShared_2399_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2398_, 1);
                    crate::leanh::lean_ctor_set(v___x_2398_, 0, v___x_2400_);
                    v___x_2402_ = v___x_2398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2403_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
                    v___x_2402_ = v_reuseFailAlloc_2403_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_msg_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2409_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_2405_, v___y_2406_, v___y_2407_);
    crate::leanh::lean_dec(v___y_2407_);
    crate::leanh::lean_dec_ref(v___y_2406_);
    return v_res_2409_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v___x_2416_: *mut crate::leanh::LeanObject,
    mut v_decl_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2422_ = l_Lean_MessageData_ofName(v___x_2416_);
    v___x_2423_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2423_, 0, v___x_2421_);
    crate::leanh::lean_ctor_set(v___x_2423_, 1, v___x_2422_);
    v___x_2424_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2425_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2423_);
    crate::leanh::lean_ctor_set(v___x_2425_, 1, v___x_2424_);
    v___x_2426_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v___x_2425_, v___y_2418_, v___y_2419_);
    return v___x_2426_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v___x_2427_: *mut crate::leanh::LeanObject,
    mut v_decl_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2432_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_2427_, v_decl_2428_, v___y_2429_, v___y_2430_);
    crate::leanh::lean_dec(v___y_2430_);
    crate::leanh::lean_dec_ref(v___y_2429_);
    crate::leanh::lean_dec(v_decl_2428_);
    return v_res_2432_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2473_ = crate::leanh::lean_unsigned_to_nat(3842861879);
    v___x_2474_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2475_ = l_Lean_Name_num___override(v___x_2474_, v___x_2473_);
    return v___x_2475_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2477_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2479_ = l_Lean_Name_str___override(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2482_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2483_ = l_Lean_Name_str___override(v___x_2482_, v___x_2481_);
    return v___x_2483_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2485_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2486_ = l_Lean_Name_num___override(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = 0;
    v___x_2497_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2498_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2499_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2500_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_2500_, 0, v___x_2499_);
    crate::leanh::lean_ctor_set(v___x_2500_, 1, v___x_2498_);
    crate::leanh::lean_ctor_set(v___x_2500_, 2, v___x_2497_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2500_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        v___x_2496_,
    );
    return v___x_2500_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2501_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___f_2502_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2503_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2504_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2503_);
    crate::leanh::lean_ctor_set(v___x_2504_, 1, v___f_2502_);
    crate::leanh::lean_ctor_set(v___x_2504_, 2, v___f_2501_);
    return v___x_2504_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2506_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2507_ = l_Lean_registerBuiltinAttribute(v___x_2506_);
    return v___x_2507_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v_a_2508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2509_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
    return v_res_2509_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2510_: *mut crate::leanh::LeanObject,
    mut v_msg_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_2511_, v___y_2512_, v___y_2513_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2516_: *mut crate::leanh::LeanObject,
    mut v_msg_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(v_00_u03b1_2516_, v_msg_2517_, v___y_2518_, v___y_2519_);
    crate::leanh::lean_dec(v___y_2519_);
    crate::leanh::lean_dec_ref(v___y_2518_);
    return v_res_2521_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2522_: *mut crate::leanh::LeanObject,
    mut v_name_2523_: *mut crate::leanh::LeanObject,
    mut v_kind_2524_: u8,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
    mut v___y_2526_: *mut crate::leanh::LeanObject,
    mut v___y_2527_: *mut crate::leanh::LeanObject,
    mut v___y_2528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_2523_, v_kind_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2531_: *mut crate::leanh::LeanObject,
    mut v_name_2532_: *mut crate::leanh::LeanObject,
    mut v_kind_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
    mut v___y_2538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_2539_: u8 = 0;
    let mut v_res_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2539_ = (crate::leanh::lean_unbox(v_kind_2533_) as u8);
    v_res_2540_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(v_00_u03b1_2531_, v_name_2532_, v_kind_boxed_2539_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
    crate::leanh::lean_dec(v___y_2537_);
    crate::leanh::lean_dec_ref(v___y_2536_);
    crate::leanh::lean_dec(v___y_2535_);
    crate::leanh::lean_dec_ref(v___y_2534_);
    return v_res_2540_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_instInhabitedCoeFnType_default = _init_l_Lean_Meta_instInhabitedCoeFnType_default();
    l_Lean_Meta_instInhabitedCoeFnType = _init_l_Lean_Meta_instInhabitedCoeFnType();
    l_Lean_Meta_instToExprCoeFnType = _init_l_Lean_Meta_instToExprCoeFnType();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instToExprCoeFnType);
    l_Lean_Meta_instToExprCoeFnInfo = _init_l_Lean_Meta_instToExprCoeFnInfo();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_instToExprCoeFnInfo);
    res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_coeExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_coeExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_FunInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CoeAttr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CoeAttr(builtin);
}
