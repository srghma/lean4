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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_instInhabitedCoeFnType_default: u8 = 0;
pub static mut l_Lean_Meta_instInhabitedCoeFnType: u8 = 0;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101,
            46, 99, 111, 101, 0,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__1_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__2_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101,
            46, 99, 111, 101, 70, 117, 110, 0,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__3_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__4_value: LeanStringObject<28> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 101, 70, 110, 84, 121, 112, 101,
            46, 99, 111, 101, 83, 111, 114, 116, 0,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnType_repr___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType_repr___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instReprCoeFnType_repr___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCoeFnType_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCoeFnType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprCoeFnType: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnType___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
                as *mut LeanObject,
            2813220318977726453 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value)
                as *mut LeanObject,
            12556370647174111156 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value)
        as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
                as *mut LeanObject,
            2813220318977726453 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__6_value)
                as *mut LeanObject,
            16398515986243675126 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
                as *mut LeanObject,
            2813220318977726453 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__9_value)
                as *mut LeanObject,
            9442608608187171560 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnType___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instToExprCoeFnType___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instToExprCoeFnType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnType___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__2_value)
            as *mut LeanObject,
        2813220318977726453 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnType___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnType___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instToExprCoeFnType___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnType___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instToExprCoeFnType: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            0 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedCoeFnInfo_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_instInhabitedCoeFnInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instInhabitedCoeFnInfo_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__10_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__12_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__15_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instReprCoeFnInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instReprCoeFnInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instReprCoeFnInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Meta_instReprCoeFnInfo: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instReprCoeFnInfo___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
                as *mut LeanObject,
            1996622761251820373 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__1_value)
                as *mut LeanObject,
            3253084188537368017 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_instToExprCoeFnInfo___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_instToExprCoeFnInfo___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_instToExprCoeFnInfo___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__0_value)
            as *mut LeanObject,
        1996622761251820373 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnInfo___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instToExprCoeFnInfo___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_instToExprCoeFnInfo: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 111, 101, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject,15884443959248703457 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value: LeanCtorObject<5> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_registerCoercion___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_registerCoercion___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_registerCoercion___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_registerCoercion___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_registerCoercion___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_registerCoercion___closed__4_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_registerCoercion___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_registerCoercion___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_registerCoercion___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_registerCoercion___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut LeanObject,72621647814721793 as *mut LeanObject,65793 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 101, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,5248179736981678329 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,16576108964040073180 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut LeanObject,10567757556072296701 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut LeanObject,14400173562802066965 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,7648651235586661436 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,2060747640412624181 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__0_value) as *mut LeanObject,12647287533329886112 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__1_value) as *mut LeanObject,16861913366284030220 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject,5178666544776117203 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__3_value) as *mut LeanObject,18011328033297698546 as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanClosureObject<3> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 3, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject] };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [65, 100, 100, 115, 32, 97, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 97, 115, 32, 97, 32, 99, 111, 101, 114, 99, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CoeFnType_ctorIdx(mut v_x_1271_: u8) -> *mut LeanObject {
    match v_x_1271_ {
        0 => {
            let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
            v___x_1272_ = lean_unsigned_to_nat(0);
            return v___x_1272_;
        }
        1 => {
            let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
            v___x_1273_ = lean_unsigned_to_nat(1);
            return v___x_1273_;
        }
        _ => {
            let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
            v___x_1274_ = lean_unsigned_to_nat(2);
            return v___x_1274_;
        }
    }
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorIdx___boxed(
    mut v_x_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1276_ = (lean_unbox(v_x_1275_) as u8);
    v_res_1277_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_boxed_1276_);
    return v_res_1277_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_toCtorIdx(mut v_x_1278_: u8) -> *mut LeanObject {
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    v___x_1279_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_1278_);
    return v___x_1279_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_toCtorIdx___boxed(
    mut v_x_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1281_: u8 = 0;
    let mut v_res_1282_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1281_ = (lean_unbox(v_x_1280_) as u8);
    v_res_1282_ = l_Lean_Meta_CoeFnType_toCtorIdx(v_x_4__boxed_1281_);
    return v_res_1282_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___redArg(
    mut v_k_1283_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1283_);
    return v_k_1283_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___redArg___boxed(
    mut v_k_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1285_: *mut LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_Lean_Meta_CoeFnType_ctorElim___redArg(v_k_1284_);
    lean_dec(v_k_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim(
    mut v_motive_1286_: *mut LeanObject,
    mut v_ctorIdx_1287_: *mut LeanObject,
    mut v_t_1288_: u8,
    mut v_h_1289_: *mut LeanObject,
    mut v_k_1290_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1290_);
    return v_k_1290_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ctorElim___boxed(
    mut v_motive_1291_: *mut LeanObject,
    mut v_ctorIdx_1292_: *mut LeanObject,
    mut v_t_1293_: *mut LeanObject,
    mut v_h_1294_: *mut LeanObject,
    mut v_k_1295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1296_: u8 = 0;
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1296_ = (lean_unbox(v_t_1293_) as u8);
    v_res_1297_ = l_Lean_Meta_CoeFnType_ctorElim(
        v_motive_1291_,
        v_ctorIdx_1292_,
        v_t_boxed_1296_,
        v_h_1294_,
        v_k_1295_,
    );
    lean_dec(v_k_1295_);
    lean_dec(v_ctorIdx_1292_);
    return v_res_1297_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___redArg(
    mut v_coe_1298_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coe_1298_);
    return v_coe_1298_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___redArg___boxed(
    mut v_coe_1299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1300_: *mut LeanObject = core::ptr::null_mut();
    v_res_1300_ = l_Lean_Meta_CoeFnType_coe_elim___redArg(v_coe_1299_);
    lean_dec(v_coe_1299_);
    return v_res_1300_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim(
    mut v_motive_1301_: *mut LeanObject,
    mut v_t_1302_: u8,
    mut v_h_1303_: *mut LeanObject,
    mut v_coe_1304_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coe_1304_);
    return v_coe_1304_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coe_elim___boxed(
    mut v_motive_1305_: *mut LeanObject,
    mut v_t_1306_: *mut LeanObject,
    mut v_h_1307_: *mut LeanObject,
    mut v_coe_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1309_ = (lean_unbox(v_t_1306_) as u8);
    v_res_1310_ =
        l_Lean_Meta_CoeFnType_coe_elim(v_motive_1305_, v_t_boxed_1309_, v_h_1307_, v_coe_1308_);
    lean_dec(v_coe_1308_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___redArg(
    mut v_coeFun_1311_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coeFun_1311_);
    return v_coeFun_1311_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___redArg___boxed(
    mut v_coeFun_1312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1313_: *mut LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_Meta_CoeFnType_coeFun_elim___redArg(v_coeFun_1312_);
    lean_dec(v_coeFun_1312_);
    return v_res_1313_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim(
    mut v_motive_1314_: *mut LeanObject,
    mut v_t_1315_: u8,
    mut v_h_1316_: *mut LeanObject,
    mut v_coeFun_1317_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coeFun_1317_);
    return v_coeFun_1317_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeFun_elim___boxed(
    mut v_motive_1318_: *mut LeanObject,
    mut v_t_1319_: *mut LeanObject,
    mut v_h_1320_: *mut LeanObject,
    mut v_coeFun_1321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1322_: u8 = 0;
    let mut v_res_1323_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1322_ = (lean_unbox(v_t_1319_) as u8);
    v_res_1323_ = l_Lean_Meta_CoeFnType_coeFun_elim(
        v_motive_1318_,
        v_t_boxed_1322_,
        v_h_1320_,
        v_coeFun_1321_,
    );
    lean_dec(v_coeFun_1321_);
    return v_res_1323_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___redArg(
    mut v_coeSort_1324_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coeSort_1324_);
    return v_coeSort_1324_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___redArg___boxed(
    mut v_coeSort_1325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1326_: *mut LeanObject = core::ptr::null_mut();
    v_res_1326_ = l_Lean_Meta_CoeFnType_coeSort_elim___redArg(v_coeSort_1325_);
    lean_dec(v_coeSort_1325_);
    return v_res_1326_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim(
    mut v_motive_1327_: *mut LeanObject,
    mut v_t_1328_: u8,
    mut v_h_1329_: *mut LeanObject,
    mut v_coeSort_1330_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_coeSort_1330_);
    return v_coeSort_1330_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_coeSort_elim___boxed(
    mut v_motive_1331_: *mut LeanObject,
    mut v_t_1332_: *mut LeanObject,
    mut v_h_1333_: *mut LeanObject,
    mut v_coeSort_1334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1335_: u8 = 0;
    let mut v_res_1336_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1335_ = (lean_unbox(v_t_1332_) as u8);
    v_res_1336_ = l_Lean_Meta_CoeFnType_coeSort_elim(
        v_motive_1331_,
        v_t_boxed_1335_,
        v_h_1333_,
        v_coeSort_1334_,
    );
    lean_dec(v_coeSort_1334_);
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
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnType_repr___closed__6() -> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1348_ = lean_unsigned_to_nat(2);
    v___x_1349_ = lean_nat_to_int(v___x_1348_);
    return v___x_1349_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnType_repr___closed__7() -> *mut LeanObject {
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1350_ = lean_unsigned_to_nat(1);
    v___x_1351_ = lean_nat_to_int(v___x_1350_);
    return v___x_1351_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnType_repr(
    mut v_x_1352_: u8,
    mut v_prec_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: u8 = 0;
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: u8 = 0;
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: u8 = 0;
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: u8 = 0;
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1352_ {
                0 => {
                    v___x_1375_ = lean_unsigned_to_nat(1024);
                    v___x_1376_ = lean_nat_dec_le(v___x_1375_, v_prec_1353_);
                    if v___x_1376_ == 0 {
                        v___x_1377_ = lean_obj_once(
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
                        v___x_1378_ = lean_obj_once(
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
                    v___x_1379_ = lean_unsigned_to_nat(1024);
                    v___x_1380_ = lean_nat_dec_le(v___x_1379_, v_prec_1353_);
                    if v___x_1380_ == 0 {
                        v___x_1381_ = lean_obj_once(
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
                        v___x_1382_ = lean_obj_once(
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
                    v___x_1383_ = lean_unsigned_to_nat(1024);
                    v___x_1384_ = lean_nat_dec_le(v___x_1383_, v_prec_1353_);
                    if v___x_1384_ == 0 {
                        v___x_1385_ = lean_obj_once(
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
                        v___x_1386_ = lean_obj_once(
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
                lean_inc(v___y_1355_);
                v___x_1357_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1357_, 0, v___y_1355_);
                lean_ctor_set(v___x_1357_, 1, v___x_1356_);
                v___x_1358_ = 0;
                v___x_1359_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1359_, 0, v___x_1357_);
                lean_ctor_set_uint8(
                    v___x_1359_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1358_,
                );
                v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1353_);
                return v___x_1360_;
            }
            2 => {
                v___x_1363_ = l_Lean_Meta_instReprCoeFnType_repr___closed__3;
                lean_inc(v___y_1362_);
                v___x_1364_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1364_, 0, v___y_1362_);
                lean_ctor_set(v___x_1364_, 1, v___x_1363_);
                v___x_1365_ = 0;
                v___x_1366_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1366_, 0, v___x_1364_);
                lean_ctor_set_uint8(
                    v___x_1366_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1365_,
                );
                v___x_1367_ = l_Repr_addAppParen(v___x_1366_, v_prec_1353_);
                return v___x_1367_;
            }
            3 => {
                v___x_1370_ = l_Lean_Meta_instReprCoeFnType_repr___closed__5;
                lean_inc(v___y_1369_);
                v___x_1371_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1371_, 0, v___y_1369_);
                lean_ctor_set(v___x_1371_, 1, v___x_1370_);
                v___x_1372_ = 0;
                v___x_1373_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1373_, 0, v___x_1371_);
                lean_ctor_set_uint8(
                    v___x_1373_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_1387_: *mut LeanObject,
    mut v_prec_1388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_1389_: u8 = 0;
    let mut v_res_1390_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1389_ = (lean_unbox(v_x_1387_) as u8);
    v_res_1390_ = l_Lean_Meta_instReprCoeFnType_repr(v_x_177__boxed_1389_, v_prec_1388_);
    lean_dec(v_prec_1388_);
    return v_res_1390_;
}
pub unsafe fn l_Lean_Meta_CoeFnType_ofNat(mut v_n_1393_: *mut LeanObject) -> u8 {
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: u8 = 0;
    v___x_1394_ = lean_unsigned_to_nat(0);
    v___x_1395_ = lean_nat_dec_le(v_n_1393_, v___x_1394_);
    if v___x_1395_ == 0 {
        let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1397_: u8 = 0;
        v___x_1396_ = lean_unsigned_to_nat(1);
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
    mut v_n_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1402_: u8 = 0;
    let mut v_r_1403_: *mut LeanObject = core::ptr::null_mut();
    v_res_1402_ = l_Lean_Meta_CoeFnType_ofNat(v_n_1401_);
    lean_dec(v_n_1401_);
    v_r_1403_ = lean_box((v_res_1402_) as usize);
    return v_r_1403_;
}
pub unsafe fn l_Lean_Meta_instDecidableEqCoeFnType(mut v_x_1404_: u8, mut v_y_1405_: u8) -> u8 {
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    v___x_1406_ = l_Lean_Meta_CoeFnType_ctorIdx(v_x_1404_);
    v___x_1407_ = l_Lean_Meta_CoeFnType_ctorIdx(v_y_1405_);
    v___x_1408_ = lean_nat_dec_eq(v___x_1406_, v___x_1407_);
    lean_dec(v___x_1407_);
    lean_dec(v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_Meta_instDecidableEqCoeFnType___boxed(
    mut v_x_1409_: *mut LeanObject,
    mut v_y_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_13__boxed_1411_: u8 = 0;
    let mut v_y_14__boxed_1412_: u8 = 0;
    let mut v_res_1413_: u8 = 0;
    let mut v_r_1414_: *mut LeanObject = core::ptr::null_mut();
    v_x_13__boxed_1411_ = (lean_unbox(v_x_1409_) as u8);
    v_y_14__boxed_1412_ = (lean_unbox(v_y_1410_) as u8);
    v_res_1413_ = l_Lean_Meta_instDecidableEqCoeFnType(v_x_13__boxed_1411_, v_y_14__boxed_1412_);
    v_r_1414_ = lean_box((v_res_1413_) as usize);
    return v_r_1414_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_box(0);
    v___x_1425_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__4;
    v___x_1426_ = l_Lean_mkConst(v___x_1425_, v___x_1424_);
    return v___x_1426_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8() -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_box(0);
    v___x_1434_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__7;
    v___x_1435_ = l_Lean_mkConst(v___x_1434_, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11() -> *mut LeanObject {
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_box(0);
    v___x_1443_ = l_Lean_Meta_instToExprCoeFnType___lam__0___closed__10;
    v___x_1444_ = l_Lean_mkConst(v___x_1443_, v___x_1442_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnType___lam__0(mut v_x_1445_: u8) -> *mut LeanObject {
    match v_x_1445_ {
        0 => {
            let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
            v___x_1446_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5,
            );
            return v___x_1446_;
        }
        1 => {
            let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
            v___x_1447_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8,
            );
            return v___x_1447_;
        }
        _ => {
            let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
            v___x_1448_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11,
            );
            return v___x_1448_;
        }
    }
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnType___lam__0___boxed(
    mut v_x_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_156__boxed_1450_: u8 = 0;
    let mut v_res_1451_: *mut LeanObject = core::ptr::null_mut();
    v_x_156__boxed_1450_ = (lean_unbox(v_x_1449_) as u8);
    v_res_1451_ = l_Lean_Meta_instToExprCoeFnType___lam__0(v_x_156__boxed_1450_);
    return v_res_1451_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___closed__2() -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_box(0);
    v___x_1458_ = l_Lean_Meta_instToExprCoeFnType___closed__1;
    v___x_1459_ = l_Lean_mkConst(v___x_1458_, v___x_1457_);
    return v___x_1459_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType___closed__3() -> *mut LeanObject {
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v___x_1460_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__2_once),
        _init_l_Lean_Meta_instToExprCoeFnType___closed__2,
    );
    v___f_1461_ = l_Lean_Meta_instToExprCoeFnType___closed__0;
    v___x_1462_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1462_, 0, v___f_1461_);
    lean_ctor_set(v___x_1462_, 1, v___x_1460_);
    return v___x_1462_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnType() -> *mut LeanObject {
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    v___x_1463_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnType___closed__3,
    );
    return v___x_1463_;
}
pub unsafe fn l_Nat_cast___at___00Lean_Meta_instReprCoeFnInfo_repr_spec__0(
    mut v_a_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
    v___x_1470_ = lean_nat_to_int(v_a_1469_);
    return v___x_1470_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
    v___x_1484_ = lean_unsigned_to_nat(11);
    v___x_1485_ = lean_nat_to_int(v___x_1484_);
    return v___x_1485_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1495_ = lean_unsigned_to_nat(8);
    v___x_1496_ = lean_nat_to_int(v___x_1495_);
    return v___x_1496_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16() -> *mut LeanObject {
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__0;
    v___x_1499_ = lean_string_length(v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__16,
    );
    v___x_1501_ = lean_nat_to_int(v___x_1500_);
    return v___x_1501_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr___redArg(
    mut v_x_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_coercee_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1509_: u8 = 0;
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: u8 = 0;
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v_numArgs_1507_ = lean_ctor_get(v_x_1506_, 0);
    lean_inc(v_numArgs_1507_);
    v_coercee_1508_ = lean_ctor_get(v_x_1506_, 1);
    lean_inc(v_coercee_1508_);
    v_type_1509_ = lean_ctor_get_uint8(
        v_x_1506_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_x_1506_);
    v___x_1510_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__5;
    v___x_1511_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__6;
    v___x_1512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__7,
    );
    v___x_1513_ = l_Nat_reprFast(v_numArgs_1507_);
    v___x_1514_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1514_, 0, v___x_1513_);
    v___x_1515_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1515_, 0, v___x_1512_);
    lean_ctor_set(v___x_1515_, 1, v___x_1514_);
    v___x_1516_ = 0;
    v___x_1517_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1517_, 0, v___x_1515_);
    lean_ctor_set_uint8(
        v___x_1517_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1518_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1518_, 0, v___x_1511_);
    lean_ctor_set(v___x_1518_, 1, v___x_1517_);
    v___x_1519_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__9;
    v___x_1520_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1520_, 0, v___x_1518_);
    lean_ctor_set(v___x_1520_, 1, v___x_1519_);
    v___x_1521_ = lean_box(1);
    v___x_1522_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1522_, 0, v___x_1520_);
    lean_ctor_set(v___x_1522_, 1, v___x_1521_);
    v___x_1523_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__11;
    v___x_1524_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1524_, 0, v___x_1522_);
    lean_ctor_set(v___x_1524_, 1, v___x_1523_);
    v___x_1525_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1525_, 0, v___x_1524_);
    lean_ctor_set(v___x_1525_, 1, v___x_1510_);
    v___x_1526_ = l_Nat_reprFast(v_coercee_1508_);
    v___x_1527_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1527_, 0, v___x_1526_);
    v___x_1528_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1528_, 0, v___x_1512_);
    lean_ctor_set(v___x_1528_, 1, v___x_1527_);
    v___x_1529_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1529_, 0, v___x_1528_);
    lean_ctor_set_uint8(
        v___x_1529_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1530_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1530_, 0, v___x_1525_);
    lean_ctor_set(v___x_1530_, 1, v___x_1529_);
    v___x_1531_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    lean_ctor_set(v___x_1531_, 1, v___x_1519_);
    v___x_1532_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1532_, 0, v___x_1531_);
    lean_ctor_set(v___x_1532_, 1, v___x_1521_);
    v___x_1533_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__13;
    v___x_1534_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1534_, 0, v___x_1532_);
    lean_ctor_set(v___x_1534_, 1, v___x_1533_);
    v___x_1535_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1535_, 0, v___x_1534_);
    lean_ctor_set(v___x_1535_, 1, v___x_1510_);
    v___x_1536_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__14,
    );
    v___x_1537_ = lean_unsigned_to_nat(0);
    v___x_1538_ = l_Lean_Meta_instReprCoeFnType_repr(v_type_1509_, v___x_1537_);
    v___x_1539_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1539_, 0, v___x_1536_);
    lean_ctor_set(v___x_1539_, 1, v___x_1538_);
    v___x_1540_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1540_, 0, v___x_1539_);
    lean_ctor_set_uint8(
        v___x_1540_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    v___x_1541_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1541_, 0, v___x_1535_);
    lean_ctor_set(v___x_1541_, 1, v___x_1540_);
    v___x_1542_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17_once),
        _init_l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__17,
    );
    v___x_1543_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__18;
    v___x_1544_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1544_, 0, v___x_1543_);
    lean_ctor_set(v___x_1544_, 1, v___x_1541_);
    v___x_1545_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg___closed__19;
    v___x_1546_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1546_, 0, v___x_1544_);
    lean_ctor_set(v___x_1546_, 1, v___x_1545_);
    v___x_1547_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1547_, 0, v___x_1542_);
    lean_ctor_set(v___x_1547_, 1, v___x_1546_);
    v___x_1548_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1548_, 0, v___x_1547_);
    lean_ctor_set_uint8(
        v___x_1548_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1516_,
    );
    return v___x_1548_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr(
    mut v_x_1549_: *mut LeanObject,
    mut v_prec_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = l_Lean_Meta_instReprCoeFnInfo_repr___redArg(v_x_1549_);
    return v___x_1551_;
}
pub unsafe fn l_Lean_Meta_instReprCoeFnInfo_repr___boxed(
    mut v_x_1552_: *mut LeanObject,
    mut v_prec_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1554_: *mut LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Lean_Meta_instReprCoeFnInfo_repr(v_x_1552_, v_prec_1553_);
    lean_dec(v_prec_1553_);
    return v_res_1554_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    v___x_1564_ = lean_box(0);
    v___x_1565_ = l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__2;
    v___x_1566_ = l_Lean_mkConst(v___x_1565_, v___x_1564_);
    return v___x_1566_;
}
pub unsafe fn l_Lean_Meta_instToExprCoeFnInfo___lam__0(
    mut v_x_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_numArgs_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_coercee_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_1570_: u8 = 0;
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v_numArgs_1568_ = lean_ctor_get(v_x_1567_, 0);
    lean_inc(v_numArgs_1568_);
    v_coercee_1569_ = lean_ctor_get(v_x_1567_, 1);
    lean_inc(v_coercee_1569_);
    v_type_1570_ = lean_ctor_get_uint8(
        v_x_1567_,
        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
    );
    lean_dec_ref(v_x_1567_);
    v___x_1571_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___lam__0___closed__3,
    );
    v___x_1572_ = l_Lean_mkNatLit(v_numArgs_1568_);
    v___x_1573_ = l_Lean_mkNatLit(v_coercee_1569_);
    match v_type_1570_ {
        0 => {
            let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
            v___x_1574_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__5,
            );
            v___x_1575_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1574_);
            return v___x_1575_;
        }
        1 => {
            let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
            v___x_1576_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__8,
            );
            v___x_1577_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1576_);
            return v___x_1577_;
        }
        _ => {
            let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
            v___x_1578_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11),
                core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11_once),
                _init_l_Lean_Meta_instToExprCoeFnType___lam__0___closed__11,
            );
            v___x_1579_ = l_Lean_mkApp3(v___x_1571_, v___x_1572_, v___x_1573_, v___x_1578_);
            return v___x_1579_;
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2() -> *mut LeanObject {
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1585_ = lean_box(0);
    v___x_1586_ = l_Lean_Meta_instToExprCoeFnInfo___closed__1;
    v___x_1587_ = l_Lean_mkConst(v___x_1586_, v___x_1585_);
    return v___x_1587_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3() -> *mut LeanObject {
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    v___x_1588_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__2_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___closed__2,
    );
    v___f_1589_ = l_Lean_Meta_instToExprCoeFnInfo___closed__0;
    v___x_1590_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1590_, 0, v___f_1589_);
    lean_ctor_set(v___x_1590_, 1, v___x_1588_);
    return v___x_1590_;
}
pub unsafe fn _init_l_Lean_Meta_instToExprCoeFnInfo() -> *mut LeanObject {
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    v___x_1591_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_instToExprCoeFnInfo___closed__3_once),
        _init_l_Lean_Meta_instToExprCoeFnInfo___closed__3,
    );
    return v___x_1591_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v_st_1592_: *mut LeanObject,
    mut v_x_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1594_ = lean_ctor_get(v_x_1593_, 0);
    lean_inc(v_fst_1594_);
    v_snd_1595_ = lean_ctor_get(v_x_1593_, 1);
    lean_inc(v_snd_1595_);
    lean_dec_ref(v_x_1593_);
    v___x_1596_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_1594_,
        v_snd_1595_,
        v_st_1592_,
    );
    return v___x_1596_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v_x_1597_: *mut LeanObject,
    mut v_a_1598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1599_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1599_, 0, v_a_1598_);
    lean_inc_ref_n(v___x_1599_, 2);
    v___x_1600_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1600_, 0, v___x_1599_);
    lean_ctor_set(v___x_1600_, 1, v___x_1599_);
    lean_ctor_set(v___x_1600_, 2, v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v_x_1601_: *mut LeanObject,
    mut v_a_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_res_1603_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v_x_1601_, v_a_1602_);
    lean_dec_ref(v_x_1601_);
    return v_res_1603_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(
    mut v___y_1604_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___y_1604_);
    return v___y_1604_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v___y_1605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1606_: *mut LeanObject = core::ptr::null_mut();
    v_res_1606_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_(v___y_1605_);
    lean_dec(v___y_1605_);
    return v_res_1606_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    v___x_1622_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_;
    v___x_1623_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2____boxed(
    mut v_a_1624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1625_: *mut LeanObject = core::ptr::null_mut();
    v_res_1625_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
    return v_res_1625_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___redArg(
    mut v_fn_1626_: *mut LeanObject,
    mut v_a_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ext_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = lean_st_ref_get(v_a_1627_);
    v_env_1630_ = lean_ctor_get(v___x_1629_, 0);
    lean_inc_ref(v_env_1630_);
    lean_dec(v___x_1629_);
    v___x_1631_ = l_Lean_Meta_coeExt;
    v_ext_1632_ = lean_ctor_get(v___x_1631_, 1);
    v_toEnvExtension_1633_ = lean_ctor_get(v_ext_1632_, 0);
    v_asyncMode_1634_ = lean_ctor_get(v_toEnvExtension_1633_, 2);
    v___x_1635_ = lean_box(1);
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
    lean_dec(v___x_1636_);
    v___x_1638_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1638_, 0, v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___redArg___boxed(
    mut v_fn_1639_: *mut LeanObject,
    mut v_a_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_1639_, v_a_1640_);
    lean_dec(v_a_1640_);
    lean_dec(v_fn_1639_);
    return v_res_1642_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f(
    mut v_fn_1643_: *mut LeanObject,
    mut v_a_1644_: *mut LeanObject,
    mut v_a_1645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_fn_1643_, v_a_1645_);
    return v___x_1647_;
}
pub unsafe fn l_Lean_Meta_getCoeFnInfo_x3f___boxed(
    mut v_fn_1648_: *mut LeanObject,
    mut v_a_1649_: *mut LeanObject,
    mut v_a_1650_: *mut LeanObject,
    mut v_a_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_Meta_getCoeFnInfo_x3f(v_fn_1648_, v_a_1649_, v_a_1650_);
    lean_dec(v_a_1650_);
    lean_dec_ref(v_a_1649_);
    lean_dec(v_fn_1648_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(
    mut v_msgData_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = lean_st_ref_get(v___y_1657_);
    v_env_1660_ = lean_ctor_get(v___x_1659_, 0);
    lean_inc_ref(v_env_1660_);
    lean_dec(v___x_1659_);
    v___x_1661_ = lean_st_ref_get(v___y_1655_);
    v_mctx_1662_ = lean_ctor_get(v___x_1661_, 0);
    lean_inc_ref(v_mctx_1662_);
    lean_dec(v___x_1661_);
    v_lctx_1663_ = lean_ctor_get(v___y_1654_, 2);
    v_options_1664_ = lean_ctor_get(v___y_1656_, 2);
    lean_inc_ref(v_options_1664_);
    lean_inc_ref(v_lctx_1663_);
    v___x_1665_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1665_, 0, v_env_1660_);
    lean_ctor_set(v___x_1665_, 1, v_mctx_1662_);
    lean_ctor_set(v___x_1665_, 2, v_lctx_1663_);
    lean_ctor_set(v___x_1665_, 3, v_options_1664_);
    v___x_1666_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1666_, 0, v___x_1665_);
    lean_ctor_set(v___x_1666_, 1, v_msgData_1653_);
    v___x_1667_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1667_, 0, v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4___boxed(
    mut v_msgData_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1674_: *mut LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msgData_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    lean_dec(v___y_1672_);
    lean_dec_ref(v___y_1671_);
    lean_dec(v___y_1670_);
    lean_dec_ref(v___y_1669_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
    mut v_msg_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
    mut v___y_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1686_: u8 = 0;
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1691_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1681_ = lean_ctor_get(v___y_1678_, 5);
                v___x_1682_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2_spec__4(v_msg_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
                v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
                v_isSharedCheck_1691_ = (!lean_is_exclusive(v___x_1682_)) as u8;
                if v_isSharedCheck_1691_ == 0 {
                    v___x_1685_ = v___x_1682_;
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1683_);
                    lean_dec(v___x_1682_);
                    v___x_1685_ = lean_box(0);
                    v_isShared_1686_ = v_isSharedCheck_1691_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1681_);
                v___x_1687_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1687_, 0, v_ref_1681_);
                lean_ctor_set(v___x_1687_, 1, v_a_1683_);
                if v_isShared_1686_ == 0 {
                    lean_ctor_set_tag(v___x_1685_, 1);
                    lean_ctor_set(v___x_1685_, 0, v___x_1687_);
                    v___x_1689_ = v___x_1685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1690_, 0, v___x_1687_);
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
    mut v_msg_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1698_: *mut LeanObject = core::ptr::null_mut();
    v_res_1698_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
        v_msg_1692_,
        v___y_1693_,
        v___y_1694_,
        v___y_1695_,
        v___y_1696_,
    );
    lean_dec(v___y_1696_);
    lean_dec_ref(v___y_1695_);
    lean_dec(v___y_1694_);
    lean_dec_ref(v___y_1693_);
    return v_res_1698_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(
    mut v_ref_1699_: *mut LeanObject,
    mut v_msg_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1718_: u8 = 0;
    let mut v_cancelTk_x3f_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1720_: u8 = 0;
    let mut v_inheritedTraceOptions_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1706_ = lean_ctor_get(v___y_1703_, 0);
    v_fileMap_1707_ = lean_ctor_get(v___y_1703_, 1);
    v_options_1708_ = lean_ctor_get(v___y_1703_, 2);
    v_currRecDepth_1709_ = lean_ctor_get(v___y_1703_, 3);
    v_maxRecDepth_1710_ = lean_ctor_get(v___y_1703_, 4);
    v_ref_1711_ = lean_ctor_get(v___y_1703_, 5);
    v_currNamespace_1712_ = lean_ctor_get(v___y_1703_, 6);
    v_openDecls_1713_ = lean_ctor_get(v___y_1703_, 7);
    v_initHeartbeats_1714_ = lean_ctor_get(v___y_1703_, 8);
    v_maxHeartbeats_1715_ = lean_ctor_get(v___y_1703_, 9);
    v_quotContext_1716_ = lean_ctor_get(v___y_1703_, 10);
    v_currMacroScope_1717_ = lean_ctor_get(v___y_1703_, 11);
    v_diag_1718_ = lean_ctor_get_uint8(
        v___y_1703_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1719_ = lean_ctor_get(v___y_1703_, 12);
    v_suppressElabErrors_1720_ = lean_ctor_get_uint8(
        v___y_1703_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1721_ = lean_ctor_get(v___y_1703_, 13);
    v_ref_1722_ = l_Lean_replaceRef(v_ref_1699_, v_ref_1711_);
    lean_inc_ref(v_inheritedTraceOptions_1721_);
    lean_inc(v_cancelTk_x3f_1719_);
    lean_inc(v_currMacroScope_1717_);
    lean_inc(v_quotContext_1716_);
    lean_inc(v_maxHeartbeats_1715_);
    lean_inc(v_initHeartbeats_1714_);
    lean_inc(v_openDecls_1713_);
    lean_inc(v_currNamespace_1712_);
    lean_inc(v_maxRecDepth_1710_);
    lean_inc(v_currRecDepth_1709_);
    lean_inc_ref(v_options_1708_);
    lean_inc_ref(v_fileMap_1707_);
    lean_inc_ref(v_fileName_1706_);
    v___x_1723_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1723_, 0, v_fileName_1706_);
    lean_ctor_set(v___x_1723_, 1, v_fileMap_1707_);
    lean_ctor_set(v___x_1723_, 2, v_options_1708_);
    lean_ctor_set(v___x_1723_, 3, v_currRecDepth_1709_);
    lean_ctor_set(v___x_1723_, 4, v_maxRecDepth_1710_);
    lean_ctor_set(v___x_1723_, 5, v_ref_1722_);
    lean_ctor_set(v___x_1723_, 6, v_currNamespace_1712_);
    lean_ctor_set(v___x_1723_, 7, v_openDecls_1713_);
    lean_ctor_set(v___x_1723_, 8, v_initHeartbeats_1714_);
    lean_ctor_set(v___x_1723_, 9, v_maxHeartbeats_1715_);
    lean_ctor_set(v___x_1723_, 10, v_quotContext_1716_);
    lean_ctor_set(v___x_1723_, 11, v_currMacroScope_1717_);
    lean_ctor_set(v___x_1723_, 12, v_cancelTk_x3f_1719_);
    lean_ctor_set(v___x_1723_, 13, v_inheritedTraceOptions_1721_);
    lean_ctor_set_uint8(
        v___x_1723_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1718_,
    );
    lean_ctor_set_uint8(
        v___x_1723_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1720_,
    );
    v___x_1724_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2___redArg(
        v_msg_1700_,
        v___y_1701_,
        v___y_1702_,
        v___x_1723_,
        v___y_1704_,
    );
    lean_dec_ref_known(v___x_1723_, 14);
    return v___x_1724_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg___boxed(
    mut v_ref_1725_: *mut LeanObject,
    mut v_msg_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
    mut v___y_1730_: *mut LeanObject,
    mut v___y_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1732_: *mut LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_1725_, v_msg_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
    lean_dec(v___y_1730_);
    lean_dec_ref(v___y_1729_);
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    lean_dec(v_ref_1725_);
    return v_res_1732_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    v___x_1733_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1733_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1734_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__0);
    v___x_1735_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1735_, 0, v___x_1734_);
    return v___x_1735_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    v___x_1736_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_1737_ = lean_unsigned_to_nat(0);
    v___x_1738_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1738_, 0, v___x_1737_);
    lean_ctor_set(v___x_1738_, 1, v___x_1737_);
    lean_ctor_set(v___x_1738_, 2, v___x_1737_);
    lean_ctor_set(v___x_1738_, 3, v___x_1737_);
    lean_ctor_set(v___x_1738_, 4, v___x_1736_);
    lean_ctor_set(v___x_1738_, 5, v___x_1736_);
    lean_ctor_set(v___x_1738_, 6, v___x_1736_);
    lean_ctor_set(v___x_1738_, 7, v___x_1736_);
    lean_ctor_set(v___x_1738_, 8, v___x_1736_);
    lean_ctor_set(v___x_1738_, 9, v___x_1736_);
    return v___x_1738_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    v___x_1739_ = lean_unsigned_to_nat(32);
    v___x_1740_ = lean_mk_empty_array_with_capacity(v___x_1739_);
    v___x_1741_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1741_, 0, v___x_1740_);
    return v___x_1741_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v___x_1742_ = 5usize;
    v___x_1743_ = lean_unsigned_to_nat(0);
    v___x_1744_ = lean_unsigned_to_nat(32);
    v___x_1745_ = lean_mk_empty_array_with_capacity(v___x_1744_);
    v___x_1746_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
    v___x_1747_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1747_, 0, v___x_1746_);
    lean_ctor_set(v___x_1747_, 1, v___x_1745_);
    lean_ctor_set(v___x_1747_, 2, v___x_1743_);
    lean_ctor_set(v___x_1747_, 3, v___x_1743_);
    lean_ctor_set_usize(v___x_1747_, 4, v___x_1742_);
    return v___x_1747_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ = lean_box(1);
    v___x_1749_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__4);
    v___x_1750_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__1);
    v___x_1751_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1751_, 0, v___x_1750_);
    lean_ctor_set(v___x_1751_, 1, v___x_1749_);
    lean_ctor_set(v___x_1751_, 2, v___x_1748_);
    return v___x_1751_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1753_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__6;
    v___x_1754_ = l_Lean_stringToMessageData(v___x_1753_);
    return v___x_1754_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__8;
    v___x_1757_ = l_Lean_stringToMessageData(v___x_1756_);
    return v___x_1757_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__10;
    v___x_1760_ = l_Lean_stringToMessageData(v___x_1759_);
    return v___x_1760_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    v___x_1762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__12;
    v___x_1763_ = l_Lean_stringToMessageData(v___x_1762_);
    return v___x_1763_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15()
-> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__14;
    v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17()
-> *mut LeanObject {
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__16;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19()
-> *mut LeanObject {
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___x_1771_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__18;
    v___x_1772_ = l_Lean_stringToMessageData(v___x_1771_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(
    mut v_msg_1773_: *mut LeanObject,
    mut v_declHint_1774_: *mut LeanObject,
    mut v___y_1775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: u8 = 0;
    let mut v_isExporting_1780_: u8 = 0;
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1802_: u8 = 0;
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: u8 = 0;
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1777_ = lean_st_ref_get(v___y_1775_);
                v_env_1778_ = lean_ctor_get(v___x_1777_, 0);
                lean_inc_ref(v_env_1778_);
                lean_dec(v___x_1777_);
                v___x_1779_ = l_Lean_Name_isAnonymous(v_declHint_1774_);
                if v___x_1779_ == 0 {
                    v_isExporting_1780_ = lean_ctor_get_uint8(
                        v_env_1778_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1780_ == 0 {
                        lean_dec_ref(v_env_1778_);
                        lean_dec(v_declHint_1774_);
                        v___x_1781_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1781_, 0, v_msg_1773_);
                        return v___x_1781_;
                    } else {
                        lean_inc_ref(v_env_1778_);
                        v___x_1782_ = l_Lean_Environment_setExporting(v_env_1778_, v___x_1779_);
                        lean_inc(v_declHint_1774_);
                        lean_inc_ref(v___x_1782_);
                        v___x_1783_ = l_Lean_Environment_contains(
                            v___x_1782_,
                            v_declHint_1774_,
                            v_isExporting_1780_,
                        );
                        if v___x_1783_ == 0 {
                            lean_dec_ref(v___x_1782_);
                            lean_dec_ref(v_env_1778_);
                            lean_dec(v_declHint_1774_);
                            v___x_1784_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1784_, 0, v_msg_1773_);
                            return v___x_1784_;
                        } else {
                            v___x_1785_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
                            v___x_1786_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
                            v___x_1787_ = l_Lean_Options_empty;
                            v___x_1788_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1788_, 0, v___x_1782_);
                            lean_ctor_set(v___x_1788_, 1, v___x_1785_);
                            lean_ctor_set(v___x_1788_, 2, v___x_1786_);
                            lean_ctor_set(v___x_1788_, 3, v___x_1787_);
                            lean_inc(v_declHint_1774_);
                            v___x_1789_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1774_, v___x_1779_);
                            v_c_1790_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1790_, 0, v___x_1788_);
                            lean_ctor_set(v_c_1790_, 1, v___x_1789_);
                            v___x_1791_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1778_,
                                v_declHint_1774_,
                            );
                            if lean_obj_tag(v___x_1791_) == 0 {
                                lean_dec_ref(v_env_1778_);
                                lean_dec(v_declHint_1774_);
                                v___x_1792_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                                v___x_1793_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1793_, 0, v___x_1792_);
                                lean_ctor_set(v___x_1793_, 1, v_c_1790_);
                                v___x_1794_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__9);
                                v___x_1795_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1795_, 0, v___x_1793_);
                                lean_ctor_set(v___x_1795_, 1, v___x_1794_);
                                v___x_1796_ = l_Lean_MessageData_note(v___x_1795_);
                                v___x_1797_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1797_, 0, v_msg_1773_);
                                lean_ctor_set(v___x_1797_, 1, v___x_1796_);
                                v___x_1798_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1798_, 0, v___x_1797_);
                                return v___x_1798_;
                            } else {
                                v_val_1799_ = lean_ctor_get(v___x_1791_, 0);
                                v_isSharedCheck_1834_ = (!lean_is_exclusive(v___x_1791_)) as u8;
                                if v_isSharedCheck_1834_ == 0 {
                                    v___x_1801_ = v___x_1791_;
                                    v_isShared_1802_ = v_isSharedCheck_1834_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1799_);
                                    lean_dec(v___x_1791_);
                                    v___x_1801_ = lean_box(0);
                                    v_isShared_1802_ = v_isSharedCheck_1834_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1778_);
                    lean_dec(v_declHint_1774_);
                    v___x_1835_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1835_, 0, v_msg_1773_);
                    return v___x_1835_;
                }
            }
            1 => {
                v___x_1803_ = lean_box(0);
                v___x_1804_ = l_Lean_Environment_header(v_env_1778_);
                lean_dec_ref(v_env_1778_);
                v___x_1805_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1804_);
                v_mod_1806_ = lean_array_get(v___x_1803_, v___x_1805_, v_val_1799_);
                lean_dec(v_val_1799_);
                lean_dec_ref(v___x_1805_);
                v___x_1807_ = l_Lean_isPrivateName(v_declHint_1774_);
                lean_dec(v_declHint_1774_);
                if v___x_1807_ == 0 {
                    v___x_1808_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__11);
                    v___x_1809_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                    lean_ctor_set(v___x_1809_, 1, v_c_1790_);
                    v___x_1810_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__13);
                    v___x_1811_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1811_, 0, v___x_1809_);
                    lean_ctor_set(v___x_1811_, 1, v___x_1810_);
                    v___x_1812_ = l_Lean_MessageData_ofName(v_mod_1806_);
                    v___x_1813_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1813_, 0, v___x_1811_);
                    lean_ctor_set(v___x_1813_, 1, v___x_1812_);
                    v___x_1814_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__15);
                    v___x_1815_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1815_, 0, v___x_1813_);
                    lean_ctor_set(v___x_1815_, 1, v___x_1814_);
                    v___x_1816_ = l_Lean_MessageData_note(v___x_1815_);
                    v___x_1817_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1817_, 0, v_msg_1773_);
                    lean_ctor_set(v___x_1817_, 1, v___x_1816_);
                    if v_isShared_1802_ == 0 {
                        lean_ctor_set_tag(v___x_1801_, 0);
                        lean_ctor_set(v___x_1801_, 0, v___x_1817_);
                        v___x_1819_ = v___x_1801_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                        v___x_1819_ = v_reuseFailAlloc_1820_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1821_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__7);
                    v___x_1822_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1822_, 0, v___x_1821_);
                    lean_ctor_set(v___x_1822_, 1, v_c_1790_);
                    v___x_1823_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__17);
                    v___x_1824_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1824_, 0, v___x_1822_);
                    lean_ctor_set(v___x_1824_, 1, v___x_1823_);
                    v___x_1825_ = l_Lean_MessageData_ofName(v_mod_1806_);
                    v___x_1826_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1826_, 0, v___x_1824_);
                    lean_ctor_set(v___x_1826_, 1, v___x_1825_);
                    v___x_1827_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__19);
                    v___x_1828_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1828_, 0, v___x_1826_);
                    lean_ctor_set(v___x_1828_, 1, v___x_1827_);
                    v___x_1829_ = l_Lean_MessageData_note(v___x_1828_);
                    v___x_1830_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1830_, 0, v_msg_1773_);
                    lean_ctor_set(v___x_1830_, 1, v___x_1829_);
                    if v_isShared_1802_ == 0 {
                        lean_ctor_set_tag(v___x_1801_, 0);
                        lean_ctor_set(v___x_1801_, 0, v___x_1830_);
                        v___x_1832_ = v___x_1801_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1830_);
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
    mut v_msg_1836_: *mut LeanObject,
    mut v_declHint_1837_: *mut LeanObject,
    mut v___y_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1840_: *mut LeanObject = core::ptr::null_mut();
    v_res_1840_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1836_, v_declHint_1837_, v___y_1838_);
    lean_dec(v___y_1838_);
    return v_res_1840_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(
    mut v_msg_1841_: *mut LeanObject,
    mut v_declHint_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1848_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_1841_, v_declHint_1842_, v___y_1846_);
                v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
                v_isSharedCheck_1858_ = (!lean_is_exclusive(v___x_1848_)) as u8;
                if v_isSharedCheck_1858_ == 0 {
                    v___x_1851_ = v___x_1848_;
                    v_isShared_1852_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1849_);
                    lean_dec(v___x_1848_);
                    v___x_1851_ = lean_box(0);
                    v_isShared_1852_ = v_isSharedCheck_1858_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1853_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1854_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1854_, 0, v___x_1853_);
                lean_ctor_set(v___x_1854_, 1, v_a_1849_);
                if v_isShared_1852_ == 0 {
                    lean_ctor_set(v___x_1851_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
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
    mut v_msg_1859_: *mut LeanObject,
    mut v_declHint_1860_: *mut LeanObject,
    mut v___y_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v___y_1863_: *mut LeanObject,
    mut v___y_1864_: *mut LeanObject,
    mut v___y_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_1859_, v_declHint_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
    lean_dec(v___y_1864_);
    lean_dec_ref(v___y_1863_);
    lean_dec(v___y_1862_);
    lean_dec_ref(v___y_1861_);
    return v_res_1866_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(
    mut v_ref_1867_: *mut LeanObject,
    mut v_msg_1868_: *mut LeanObject,
    mut v_declHint_1869_: *mut LeanObject,
    mut v___y_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
    mut v___y_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8(v_msg_1868_, v_declHint_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
    v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
    lean_inc(v_a_1876_);
    lean_dec_ref(v___x_1875_);
    v___x_1877_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_1867_, v_a_1876_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
    return v___x_1877_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg___boxed(
    mut v_ref_1878_: *mut LeanObject,
    mut v_msg_1879_: *mut LeanObject,
    mut v_declHint_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
    mut v___y_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1886_: *mut LeanObject = core::ptr::null_mut();
    v_res_1886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1878_, v_msg_1879_, v_declHint_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_);
    lean_dec(v___y_1884_);
    lean_dec_ref(v___y_1883_);
    lean_dec(v___y_1882_);
    lean_dec_ref(v___y_1881_);
    lean_dec(v_ref_1878_);
    return v_res_1886_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    v___x_1888_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__0;
    v___x_1889_ = l_Lean_stringToMessageData(v___x_1888_);
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__2;
    v___x_1892_ = l_Lean_stringToMessageData(v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_ref_1893_: *mut LeanObject,
    mut v_constName_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
    mut v___y_1896_: *mut LeanObject,
    mut v___y_1897_: *mut LeanObject,
    mut v___y_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1900_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__1);
    v___x_1901_ = 0;
    lean_inc(v_constName_1894_);
    v___x_1902_ = l_Lean_MessageData_ofConstName(v_constName_1894_, v___x_1901_);
    v___x_1903_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1903_, 0, v___x_1900_);
    lean_ctor_set(v___x_1903_, 1, v___x_1902_);
    v___x_1904_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
    v___x_1905_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1905_, 0, v___x_1903_);
    lean_ctor_set(v___x_1905_, 1, v___x_1904_);
    v___x_1906_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_1893_, v___x_1905_, v_constName_1894_, v___y_1895_, v___y_1896_, v___y_1897_, v___y_1898_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___boxed(
    mut v_ref_1907_: *mut LeanObject,
    mut v_constName_1908_: *mut LeanObject,
    mut v___y_1909_: *mut LeanObject,
    mut v___y_1910_: *mut LeanObject,
    mut v___y_1911_: *mut LeanObject,
    mut v___y_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1914_: *mut LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1907_, v_constName_1908_, v___y_1909_, v___y_1910_, v___y_1911_, v___y_1912_);
    lean_dec(v___y_1912_);
    lean_dec_ref(v___y_1911_);
    lean_dec(v___y_1910_);
    lean_dec_ref(v___y_1909_);
    lean_dec(v_ref_1907_);
    return v_res_1914_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(
    mut v_constName_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
    mut v___y_1917_: *mut LeanObject,
    mut v___y_1918_: *mut LeanObject,
    mut v___y_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1921_ = lean_ctor_get(v___y_1918_, 5);
    v___x_1922_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_1921_, v_constName_1915_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_constName_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
    lean_dec(v___y_1927_);
    lean_dec_ref(v___y_1926_);
    lean_dec(v___y_1925_);
    lean_dec_ref(v___y_1924_);
    return v_res_1929_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(
    mut v_constName_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1936_ = lean_st_ref_get(v___y_1934_);
                v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
                lean_inc_ref(v_env_1937_);
                lean_dec(v___x_1936_);
                v___x_1938_ = 0;
                lean_inc(v_constName_1930_);
                v___x_1939_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_1937_,
                    v_constName_1930_,
                    v___x_1938_,
                );
                if lean_obj_tag(v___x_1939_) == 0 {
                    v___x_1940_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_);
                    return v___x_1940_;
                } else {
                    lean_dec(v_constName_1930_);
                    v_val_1941_ = lean_ctor_get(v___x_1939_, 0);
                    v_isSharedCheck_1948_ = (!lean_is_exclusive(v___x_1939_)) as u8;
                    if v_isSharedCheck_1948_ == 0 {
                        v___x_1943_ = v___x_1939_;
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1941_);
                        lean_dec(v___x_1939_);
                        v___x_1943_ = lean_box(0);
                        v_isShared_1944_ = v_isSharedCheck_1948_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1944_ == 0 {
                    lean_ctor_set_tag(v___x_1943_, 0);
                    v___x_1946_ = v___x_1943_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_val_1941_);
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
    mut v_constName_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1955_: *mut LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
    lean_dec(v___y_1953_);
    lean_dec_ref(v___y_1952_);
    lean_dec(v___y_1951_);
    lean_dec_ref(v___y_1950_);
    return v_res_1955_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(
    mut v_a_1956_: *mut LeanObject,
    mut v_a_1957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1956_) == 0 {
                    v___x_1958_ = l_List_reverse___redArg(v_a_1957_);
                    return v___x_1958_;
                } else {
                    v_head_1959_ = lean_ctor_get(v_a_1956_, 0);
                    v_tail_1960_ = lean_ctor_get(v_a_1956_, 1);
                    v_isSharedCheck_1969_ = (!lean_is_exclusive(v_a_1956_)) as u8;
                    if v_isSharedCheck_1969_ == 0 {
                        v___x_1962_ = v_a_1956_;
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1960_);
                        lean_inc(v_head_1959_);
                        lean_dec(v_a_1956_);
                        v___x_1962_ = lean_box(0);
                        v_isShared_1963_ = v_isSharedCheck_1969_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1964_ = l_Lean_mkLevelParam(v_head_1959_);
                if v_isShared_1963_ == 0 {
                    lean_ctor_set(v___x_1962_, 1, v_a_1957_);
                    lean_ctor_set(v___x_1962_, 0, v___x_1964_);
                    v___x_1966_ = v___x_1962_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1968_, 0, v___x_1964_);
                    lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_a_1957_);
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
    mut v_constName_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1980_: u8 = 0;
    let mut v_levelParams_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_a_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1992_: u8 = 0;
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_constName_1970_);
                v___x_1976_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0(v_constName_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
                if lean_obj_tag(v___x_1976_) == 0 {
                    v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1988_ = (!lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1988_ == 0 {
                        v___x_1979_ = v___x_1976_;
                        v_isShared_1980_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1977_);
                        lean_dec(v___x_1976_);
                        v___x_1979_ = lean_box(0);
                        v_isShared_1980_ = v_isSharedCheck_1988_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_constName_1970_);
                    v_a_1989_ = lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1996_ = (!lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1996_ == 0 {
                        v___x_1991_ = v___x_1976_;
                        v_isShared_1992_ = v_isSharedCheck_1996_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1989_);
                        lean_dec(v___x_1976_);
                        v___x_1991_ = lean_box(0);
                        v_isShared_1992_ = v_isSharedCheck_1996_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_1981_ = lean_ctor_get(v_a_1977_, 1);
                lean_inc(v_levelParams_1981_);
                lean_dec(v_a_1977_);
                v___x_1982_ = lean_box(0);
                v___x_1983_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__1(v_levelParams_1981_, v___x_1982_);
                v___x_1984_ = l_Lean_mkConst(v_constName_1970_, v___x_1983_);
                if v_isShared_1980_ == 0 {
                    lean_ctor_set(v___x_1979_, 0, v___x_1984_);
                    v___x_1986_ = v___x_1979_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1984_);
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
                    v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_a_1989_);
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
    mut v_constName_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2003_: *mut LeanObject = core::ptr::null_mut();
    v_res_2003_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(
        v_constName_1997_,
        v___y_1998_,
        v___y_1999_,
        v___y_2000_,
        v___y_2001_,
    );
    lean_dec(v___y_2001_);
    lean_dec_ref(v___y_2000_);
    lean_dec(v___y_1999_);
    lean_dec_ref(v___y_1998_);
    return v_res_2003_;
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(
    mut v_as_2004_: *mut LeanObject,
    mut v_j_2005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: u8 = 0;
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_2010_: u8 = 0;
    let mut v___x_2011_: u8 = 0;
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2006_ = lean_array_get_size(v_as_2004_);
                v___x_2007_ = lean_nat_dec_lt(v_j_2005_, v___x_2006_);
                if v___x_2007_ == 0 {
                    lean_dec(v_j_2005_);
                    v___x_2008_ = lean_box(0);
                    return v___x_2008_;
                } else {
                    v___x_2009_ = lean_array_fget_borrowed(v_as_2004_, v_j_2005_);
                    v_binderInfo_2010_ = lean_ctor_get_uint8(
                        v___x_2009_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_2011_ = l_Lean_BinderInfo_isExplicit(v_binderInfo_2010_);
                    if v___x_2011_ == 0 {
                        v___x_2012_ = lean_unsigned_to_nat(1);
                        v___x_2013_ = lean_nat_add(v_j_2005_, v___x_2012_);
                        lean_dec(v_j_2005_);
                        v_j_2005_ = v___x_2013_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2015_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2015_, 0, v_j_2005_);
                        return v___x_2015_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1___boxed(
    mut v_as_2016_: *mut LeanObject,
    mut v_j_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2018_: *mut LeanObject = core::ptr::null_mut();
    v_res_2018_ =
        l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(v_as_2016_, v_j_2017_);
    lean_dec_ref(v_as_2016_);
    return v_res_2018_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__0() -> *mut LeanObject {
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    v___x_2019_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2019_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__1() -> *mut LeanObject {
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    v___x_2020_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__0_once),
        _init_l_Lean_Meta_registerCoercion___closed__0,
    );
    v___x_2021_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2021_, 0, v___x_2020_);
    return v___x_2021_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__2() -> *mut LeanObject {
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2022_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1_once),
        _init_l_Lean_Meta_registerCoercion___closed__1,
    );
    v___x_2023_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2023_, 0, v___x_2022_);
    lean_ctor_set(v___x_2023_, 1, v___x_2022_);
    return v___x_2023_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__3() -> *mut LeanObject {
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    v___x_2024_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__1_once),
        _init_l_Lean_Meta_registerCoercion___closed__1,
    );
    v___x_2025_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2025_, 0, v___x_2024_);
    lean_ctor_set(v___x_2025_, 1, v___x_2024_);
    lean_ctor_set(v___x_2025_, 2, v___x_2024_);
    lean_ctor_set(v___x_2025_, 3, v___x_2024_);
    lean_ctor_set(v___x_2025_, 4, v___x_2024_);
    lean_ctor_set(v___x_2025_, 5, v___x_2024_);
    return v___x_2025_;
}
pub unsafe fn _init_l_Lean_Meta_registerCoercion___closed__5() -> *mut LeanObject {
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    v___x_2027_ = l_Lean_Meta_registerCoercion___closed__4;
    v___x_2028_ = l_Lean_stringToMessageData(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_Meta_registerCoercion(
    mut v_name_2029_: *mut LeanObject,
    mut v_info_2030_: *mut LeanObject,
    mut v_a_2031_: *mut LeanObject,
    mut v_a_2032_: *mut LeanObject,
    mut v_a_2033_: *mut LeanObject,
    mut v_a_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_info_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2066_: u8 = 0;
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut v_unused_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramInfo_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2087_: u8 = 0;
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2103_: u8 = 0;
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2107_: u8 = 0;
    let mut v_reuseFailAlloc_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2109_: u8 = 0;
    let mut v_unused_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_a_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2126_: u8 = 0;
    let mut v_val_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_2030_) == 0 {
                    lean_inc(v_name_2029_);
                    v___x_2079_ =
                        l_Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0(
                            v_name_2029_,
                            v_a_2031_,
                            v_a_2032_,
                            v_a_2033_,
                            v_a_2034_,
                        );
                    if lean_obj_tag(v___x_2079_) == 0 {
                        v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
                        lean_inc(v_a_2080_);
                        lean_dec_ref_known(v___x_2079_, 1);
                        v___x_2081_ = lean_box(0);
                        v___x_2082_ = l_Lean_Meta_getFunInfo(
                            v_a_2080_,
                            v___x_2081_,
                            v_a_2031_,
                            v_a_2032_,
                            v_a_2033_,
                            v_a_2034_,
                        );
                        if lean_obj_tag(v___x_2082_) == 0 {
                            v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
                            lean_inc(v_a_2083_);
                            lean_dec_ref_known(v___x_2082_, 1);
                            v_paramInfo_2084_ = lean_ctor_get(v_a_2083_, 0);
                            v_isSharedCheck_2109_ = (!lean_is_exclusive(v_a_2083_)) as u8;
                            if v_isSharedCheck_2109_ == 0 {
                                v_unused_2110_ = lean_ctor_get(v_a_2083_, 1);
                                lean_dec(v_unused_2110_);
                                v___x_2086_ = v_a_2083_;
                                v_isShared_2087_ = v_isSharedCheck_2109_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_paramInfo_2084_);
                                lean_dec(v_a_2083_);
                                v___x_2086_ = lean_box(0);
                                v_isShared_2087_ = v_isSharedCheck_2109_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec(v_name_2029_);
                            v_a_2111_ = lean_ctor_get(v___x_2082_, 0);
                            v_isSharedCheck_2118_ = (!lean_is_exclusive(v___x_2082_)) as u8;
                            if v_isSharedCheck_2118_ == 0 {
                                v___x_2113_ = v___x_2082_;
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2111_);
                                lean_dec(v___x_2082_);
                                v___x_2113_ = lean_box(0);
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_name_2029_);
                        v_a_2119_ = lean_ctor_get(v___x_2079_, 0);
                        v_isSharedCheck_2126_ = (!lean_is_exclusive(v___x_2079_)) as u8;
                        if v_isSharedCheck_2126_ == 0 {
                            v___x_2121_ = v___x_2079_;
                            v_isShared_2122_ = v_isSharedCheck_2126_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2119_);
                            lean_dec(v___x_2079_);
                            v___x_2121_ = lean_box(0);
                            v_isShared_2122_ = v_isSharedCheck_2126_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    v_val_2127_ = lean_ctor_get(v_info_2030_, 0);
                    lean_inc(v_val_2127_);
                    lean_dec_ref_known(v_info_2030_, 1);
                    v_info_2037_ = v_val_2127_;
                    v___y_2038_ = v_a_2032_;
                    v___y_2039_ = v_a_2034_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2040_ = lean_st_ref_take(v___y_2039_);
                v_env_2041_ = lean_ctor_get(v___x_2040_, 0);
                v_nextMacroScope_2042_ = lean_ctor_get(v___x_2040_, 1);
                v_ngen_2043_ = lean_ctor_get(v___x_2040_, 2);
                v_auxDeclNGen_2044_ = lean_ctor_get(v___x_2040_, 3);
                v_traceState_2045_ = lean_ctor_get(v___x_2040_, 4);
                v_messages_2046_ = lean_ctor_get(v___x_2040_, 6);
                v_infoState_2047_ = lean_ctor_get(v___x_2040_, 7);
                v_snapshotTasks_2048_ = lean_ctor_get(v___x_2040_, 8);
                v_isSharedCheck_2077_ = (!lean_is_exclusive(v___x_2040_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = lean_ctor_get(v___x_2040_, 5);
                    lean_dec(v_unused_2078_);
                    v___x_2050_ = v___x_2040_;
                    v_isShared_2051_ = v_isSharedCheck_2077_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2048_);
                    lean_inc(v_infoState_2047_);
                    lean_inc(v_messages_2046_);
                    lean_inc(v_traceState_2045_);
                    lean_inc(v_auxDeclNGen_2044_);
                    lean_inc(v_ngen_2043_);
                    lean_inc(v_nextMacroScope_2042_);
                    lean_inc(v_env_2041_);
                    lean_dec(v___x_2040_);
                    v___x_2050_ = lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2077_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2052_ = l_Lean_Meta_coeExt;
                v___x_2053_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2053_, 0, v_name_2029_);
                lean_ctor_set(v___x_2053_, 1, v_info_2037_);
                v___x_2054_ = l_Lean_ScopedEnvExtension_addEntry___redArg(
                    v___x_2052_,
                    v_env_2041_,
                    v___x_2053_,
                );
                v___x_2055_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__2_once),
                    _init_l_Lean_Meta_registerCoercion___closed__2,
                );
                if v_isShared_2051_ == 0 {
                    lean_ctor_set(v___x_2050_, 5, v___x_2055_);
                    lean_ctor_set(v___x_2050_, 0, v___x_2054_);
                    v___x_2057_ = v___x_2050_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2054_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 1, v_nextMacroScope_2042_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 2, v_ngen_2043_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 3, v_auxDeclNGen_2044_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 4, v_traceState_2045_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 5, v___x_2055_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 6, v_messages_2046_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 7, v_infoState_2047_);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 8, v_snapshotTasks_2048_);
                    v___x_2057_ = v_reuseFailAlloc_2076_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2058_ = lean_st_ref_set(v___y_2039_, v___x_2057_);
                v___x_2059_ = lean_st_ref_take(v___y_2038_);
                v_mctx_2060_ = lean_ctor_get(v___x_2059_, 0);
                v_zetaDeltaFVarIds_2061_ = lean_ctor_get(v___x_2059_, 2);
                v_postponed_2062_ = lean_ctor_get(v___x_2059_, 3);
                v_diag_2063_ = lean_ctor_get(v___x_2059_, 4);
                v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_2059_)) as u8;
                if v_isSharedCheck_2074_ == 0 {
                    v_unused_2075_ = lean_ctor_get(v___x_2059_, 1);
                    lean_dec(v_unused_2075_);
                    v___x_2065_ = v___x_2059_;
                    v_isShared_2066_ = v_isSharedCheck_2074_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_2063_);
                    lean_inc(v_postponed_2062_);
                    lean_inc(v_zetaDeltaFVarIds_2061_);
                    lean_inc(v_mctx_2060_);
                    lean_dec(v___x_2059_);
                    v___x_2065_ = lean_box(0);
                    v_isShared_2066_ = v_isSharedCheck_2074_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2067_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__3_once),
                    _init_l_Lean_Meta_registerCoercion___closed__3,
                );
                if v_isShared_2066_ == 0 {
                    lean_ctor_set(v___x_2065_, 1, v___x_2067_);
                    v___x_2069_ = v___x_2065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_mctx_2060_);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___x_2067_);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 2, v_zetaDeltaFVarIds_2061_);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 3, v_postponed_2062_);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 4, v_diag_2063_);
                    v___x_2069_ = v_reuseFailAlloc_2073_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2070_ = lean_st_ref_set(v___y_2038_, v___x_2069_);
                v___x_2071_ = lean_box(0);
                v___x_2072_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2072_, 0, v___x_2071_);
                return v___x_2072_;
            }
            6 => {
                v___x_2088_ = lean_unsigned_to_nat(0);
                v___x_2089_ = l_Array_findIdx_x3f_loop___at___00Lean_Meta_registerCoercion_spec__1(
                    v_paramInfo_2084_,
                    v___x_2088_,
                );
                lean_dec_ref(v_paramInfo_2084_);
                if lean_obj_tag(v___x_2089_) == 1 {
                    lean_del_object(v___x_2086_);
                    v_val_2090_ = lean_ctor_get(v___x_2089_, 0);
                    lean_inc(v_val_2090_);
                    lean_dec_ref_known(v___x_2089_, 1);
                    v___x_2091_ = lean_unsigned_to_nat(1);
                    v___x_2092_ = lean_nat_add(v_val_2090_, v___x_2091_);
                    v___x_2093_ = 0;
                    v___x_2094_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_2094_, 0, v___x_2092_);
                    lean_ctor_set(v___x_2094_, 1, v_val_2090_);
                    lean_ctor_set_uint8(
                        v___x_2094_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_2093_,
                    );
                    v_info_2037_ = v___x_2094_;
                    v___y_2038_ = v_a_2032_;
                    v___y_2039_ = v_a_2034_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2089_);
                    v___x_2095_ = l_Lean_MessageData_ofName(v_name_2029_);
                    v___x_2096_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__5),
                        core::ptr::addr_of_mut!(l_Lean_Meta_registerCoercion___closed__5_once),
                        _init_l_Lean_Meta_registerCoercion___closed__5,
                    );
                    if v_isShared_2087_ == 0 {
                        lean_ctor_set_tag(v___x_2086_, 7);
                        lean_ctor_set(v___x_2086_, 1, v___x_2096_);
                        lean_ctor_set(v___x_2086_, 0, v___x_2095_);
                        v___x_2098_ = v___x_2086_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2108_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2095_);
                        lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2096_);
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
                v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
                v_isSharedCheck_2107_ = (!lean_is_exclusive(v___x_2099_)) as u8;
                if v_isSharedCheck_2107_ == 0 {
                    v___x_2102_ = v___x_2099_;
                    v_isShared_2103_ = v_isSharedCheck_2107_;
                    state = 8;
                    continue;
                } else {
                    lean_inc(v_a_2100_);
                    lean_dec(v___x_2099_);
                    v___x_2102_ = lean_box(0);
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
                    v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
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
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
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
                    v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
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
    mut v_name_2128_: *mut LeanObject,
    mut v_info_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2135_: *mut LeanObject = core::ptr::null_mut();
    v_res_2135_ = l_Lean_Meta_registerCoercion(
        v_name_2128_,
        v_info_2129_,
        v_a_2130_,
        v_a_2131_,
        v_a_2132_,
        v_a_2133_,
    );
    lean_dec(v_a_2133_);
    lean_dec_ref(v_a_2132_);
    lean_dec(v_a_2131_);
    lean_dec_ref(v_a_2130_);
    return v_res_2135_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(
    mut v_00_u03b1_2136_: *mut LeanObject,
    mut v_msg_2137_: *mut LeanObject,
    mut v___y_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v___y_2140_: *mut LeanObject,
    mut v___y_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2144_: *mut LeanObject,
    mut v_msg_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v___y_2147_: *mut LeanObject,
    mut v___y_2148_: *mut LeanObject,
    mut v___y_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2151_: *mut LeanObject = core::ptr::null_mut();
    v_res_2151_ = l_Lean_throwError___at___00Lean_Meta_registerCoercion_spec__2(
        v_00_u03b1_2144_,
        v_msg_2145_,
        v___y_2146_,
        v___y_2147_,
        v___y_2148_,
        v___y_2149_,
    );
    lean_dec(v___y_2149_);
    lean_dec_ref(v___y_2148_);
    lean_dec(v___y_2147_);
    lean_dec_ref(v___y_2146_);
    return v_res_2151_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2152_: *mut LeanObject,
    mut v_constName_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
    mut v___y_2156_: *mut LeanObject,
    mut v___y_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    v___x_2159_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___redArg(v_constName_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_);
    return v___x_2159_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2160_: *mut LeanObject,
    mut v_constName_2161_: *mut LeanObject,
    mut v___y_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v___y_2165_: *mut LeanObject,
    mut v___y_2166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2167_: *mut LeanObject = core::ptr::null_mut();
    v_res_2167_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1(v_00_u03b1_2160_, v_constName_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
    lean_dec(v___y_2165_);
    lean_dec_ref(v___y_2164_);
    lean_dec(v___y_2163_);
    lean_dec_ref(v___y_2162_);
    return v_res_2167_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b1_2168_: *mut LeanObject,
    mut v_ref_2169_: *mut LeanObject,
    mut v_constName_2170_: *mut LeanObject,
    mut v___y_2171_: *mut LeanObject,
    mut v___y_2172_: *mut LeanObject,
    mut v___y_2173_: *mut LeanObject,
    mut v___y_2174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    v___x_2176_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg(v_ref_2169_, v_constName_2170_, v___y_2171_, v___y_2172_, v___y_2173_, v___y_2174_);
    return v___x_2176_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___boxed(
    mut v_00_u03b1_2177_: *mut LeanObject,
    mut v_ref_2178_: *mut LeanObject,
    mut v_constName_2179_: *mut LeanObject,
    mut v___y_2180_: *mut LeanObject,
    mut v___y_2181_: *mut LeanObject,
    mut v___y_2182_: *mut LeanObject,
    mut v___y_2183_: *mut LeanObject,
    mut v___y_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5(v_00_u03b1_2177_, v_ref_2178_, v_constName_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
    lean_dec(v___y_2183_);
    lean_dec_ref(v___y_2182_);
    lean_dec(v___y_2181_);
    lean_dec_ref(v___y_2180_);
    lean_dec(v_ref_2178_);
    return v_res_2185_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(
    mut v_00_u03b1_2186_: *mut LeanObject,
    mut v_ref_2187_: *mut LeanObject,
    mut v_msg_2188_: *mut LeanObject,
    mut v_declHint_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    v___x_2195_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___redArg(v_ref_2187_, v_msg_2188_, v_declHint_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
    return v___x_2195_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7___boxed(
    mut v_00_u03b1_2196_: *mut LeanObject,
    mut v_ref_2197_: *mut LeanObject,
    mut v_msg_2198_: *mut LeanObject,
    mut v_declHint_2199_: *mut LeanObject,
    mut v___y_2200_: *mut LeanObject,
    mut v___y_2201_: *mut LeanObject,
    mut v___y_2202_: *mut LeanObject,
    mut v___y_2203_: *mut LeanObject,
    mut v___y_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2205_: *mut LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7(v_00_u03b1_2196_, v_ref_2197_, v_msg_2198_, v_declHint_2199_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
    lean_dec(v___y_2203_);
    lean_dec_ref(v___y_2202_);
    lean_dec(v___y_2201_);
    lean_dec_ref(v___y_2200_);
    lean_dec(v_ref_2197_);
    return v_res_2205_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(
    mut v_msg_2206_: *mut LeanObject,
    mut v_declHint_2207_: *mut LeanObject,
    mut v___y_2208_: *mut LeanObject,
    mut v___y_2209_: *mut LeanObject,
    mut v___y_2210_: *mut LeanObject,
    mut v___y_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    v___x_2213_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg(v_msg_2206_, v_declHint_2207_, v___y_2211_);
    return v___x_2213_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___boxed(
    mut v_msg_2214_: *mut LeanObject,
    mut v_declHint_2215_: *mut LeanObject,
    mut v___y_2216_: *mut LeanObject,
    mut v___y_2217_: *mut LeanObject,
    mut v___y_2218_: *mut LeanObject,
    mut v___y_2219_: *mut LeanObject,
    mut v___y_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2221_: *mut LeanObject = core::ptr::null_mut();
    v_res_2221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9(v_msg_2214_, v_declHint_2215_, v___y_2216_, v___y_2217_, v___y_2218_, v___y_2219_);
    lean_dec(v___y_2219_);
    lean_dec_ref(v___y_2218_);
    lean_dec(v___y_2217_);
    lean_dec_ref(v___y_2216_);
    return v_res_2221_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(
    mut v_00_u03b1_2222_: *mut LeanObject,
    mut v_ref_2223_: *mut LeanObject,
    mut v_msg_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    v___x_2230_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___redArg(v_ref_2223_, v_msg_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
    return v___x_2230_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9___boxed(
    mut v_00_u03b1_2231_: *mut LeanObject,
    mut v_ref_2232_: *mut LeanObject,
    mut v_msg_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
    mut v___y_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2239_: *mut LeanObject = core::ptr::null_mut();
    v_res_2239_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__9(v_00_u03b1_2231_, v_ref_2232_, v_msg_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
    lean_dec(v___y_2237_);
    lean_dec_ref(v___y_2236_);
    lean_dec(v___y_2235_);
    lean_dec_ref(v___y_2234_);
    lean_dec(v_ref_2232_);
    return v_res_2239_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v_decl_2240_: *mut LeanObject,
    mut v_____r_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    v___x_2247_ = lean_box(0);
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
    mut v_decl_2249_: *mut LeanObject,
    mut v_____r_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
    v_res_2256_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_2249_, v_____r_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
    lean_dec(v___y_2254_);
    lean_dec_ref(v___y_2253_);
    lean_dec(v___y_2252_);
    lean_dec_ref(v___y_2251_);
    return v_res_2256_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2258_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__0;
    v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
    return v___x_2259_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    v___x_2261_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__2;
    v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
    return v___x_2262_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(
    mut v_name_2266_: *mut LeanObject,
    mut v_kind_2267_: u8,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
    mut v___y_2270_: *mut LeanObject,
    mut v___y_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2273_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__1);
                v___x_2274_ = l_Lean_MessageData_ofName(v_name_2266_);
                v___x_2275_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2275_, 0, v___x_2273_);
                lean_ctor_set(v___x_2275_, 1, v___x_2274_);
                v___x_2276_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg___closed__3);
                v___x_2277_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2277_, 0, v___x_2275_);
                lean_ctor_set(v___x_2277_, 1, v___x_2276_);
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
                lean_inc_ref(v___y_2279_);
                v___x_2280_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2280_, 0, v___y_2279_);
                v___x_2281_ = l_Lean_MessageData_ofFormat(v___x_2280_);
                v___x_2282_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2282_, 0, v___x_2277_);
                lean_ctor_set(v___x_2282_, 1, v___x_2281_);
                v___x_2283_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5___redArg___closed__3);
                v___x_2284_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2284_, 0, v___x_2282_);
                lean_ctor_set(v___x_2284_, 1, v___x_2283_);
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
    mut v_name_2289_: *mut LeanObject,
    mut v_kind_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
    mut v___y_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
    mut v___y_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2296_ = (lean_unbox(v_kind_2290_) as u8);
    v_res_2297_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_2289_, v_kind_boxed_2296_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
    lean_dec(v___y_2294_);
    lean_dec_ref(v___y_2293_);
    lean_dec(v___y_2292_);
    lean_dec_ref(v___y_2291_);
    return v_res_2297_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: u64 = 0;
    v___x_2304_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2305_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2304_);
    return v___x_2305_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2306_: u64 = 0;
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    v___x_2306_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2307_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2308_ = lean_alloc_ctor(0, 1, (8) as u32);
    lean_ctor_set(v___x_2308_, 0, v___x_2307_);
    lean_ctor_set_uint64(
        v___x_2308_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_2306_,
    );
    return v___x_2308_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2309_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    v___x_2310_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2311_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v___x_2310_);
    return v___x_2311_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2313_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_2313_, 0, v___x_2312_);
    lean_ctor_set(v___x_2313_, 1, v___x_2312_);
    lean_ctor_set(v___x_2313_, 2, v___x_2312_);
    lean_ctor_set(v___x_2313_, 3, v___x_2312_);
    lean_ctor_set(v___x_2313_, 4, v___x_2312_);
    lean_ctor_set(v___x_2313_, 5, v___x_2312_);
    return v___x_2313_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2314_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2315_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2315_, 0, v___x_2314_);
    lean_ctor_set(v___x_2315_, 1, v___x_2314_);
    lean_ctor_set(v___x_2315_, 2, v___x_2314_);
    lean_ctor_set(v___x_2315_, 3, v___x_2314_);
    lean_ctor_set(v___x_2315_, 4, v___x_2314_);
    return v___x_2315_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v___x_2316_: *mut LeanObject,
    mut v___x_2317_: *mut LeanObject,
    mut v___x_2318_: *mut LeanObject,
    mut v_decl_2319_: *mut LeanObject,
    mut v___stx_2320_: *mut LeanObject,
    mut v_kind_2321_: u8,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: u8 = 0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: usize = 0;
    let mut v___x_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: u8 = 0;
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2325_ = 1;
                v___x_2326_ = 0;
                v___x_2327_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2328_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__4_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2329_ = lean_unsigned_to_nat(32);
                v___x_2330_ = lean_mk_empty_array_with_capacity(v___x_2329_);
                v___x_2331_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__3);
                v___x_2332_ = 5usize;
                lean_inc_n(v___x_2316_, 6);
                v___x_2333_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
                lean_ctor_set(v___x_2333_, 0, v___x_2331_);
                lean_ctor_set(v___x_2333_, 1, v___x_2330_);
                lean_ctor_set(v___x_2333_, 2, v___x_2316_);
                lean_ctor_set(v___x_2333_, 3, v___x_2316_);
                lean_ctor_set_usize(v___x_2333_, 4, v___x_2332_);
                v___x_2334_ = lean_box(1);
                lean_inc_ref(v___x_2333_);
                v___x_2335_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2335_, 0, v___x_2328_);
                lean_ctor_set(v___x_2335_, 1, v___x_2333_);
                lean_ctor_set(v___x_2335_, 2, v___x_2334_);
                v___x_2336_ = lean_mk_empty_array_with_capacity(v___x_2316_);
                v___x_2337_ = lean_box(0);
                lean_inc(v___x_2317_);
                v___x_2338_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2338_, 0, v___x_2327_);
                lean_ctor_set(v___x_2338_, 1, v___x_2317_);
                lean_ctor_set(v___x_2338_, 2, v___x_2335_);
                lean_ctor_set(v___x_2338_, 3, v___x_2336_);
                lean_ctor_set(v___x_2338_, 4, v___x_2337_);
                lean_ctor_set(v___x_2338_, 5, v___x_2316_);
                lean_ctor_set(v___x_2338_, 6, v___x_2337_);
                lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v___x_2326_,
                );
                lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v___x_2326_,
                );
                lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v___x_2326_,
                );
                lean_ctor_set_uint8(
                    v___x_2338_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v___x_2325_,
                );
                v___x_2339_ = lean_alloc_ctor(0, 10, (0) as u32);
                lean_ctor_set(v___x_2339_, 0, v___x_2316_);
                lean_ctor_set(v___x_2339_, 1, v___x_2316_);
                lean_ctor_set(v___x_2339_, 2, v___x_2316_);
                lean_ctor_set(v___x_2339_, 3, v___x_2316_);
                lean_ctor_set(v___x_2339_, 4, v___x_2328_);
                lean_ctor_set(v___x_2339_, 5, v___x_2328_);
                lean_ctor_set(v___x_2339_, 6, v___x_2328_);
                lean_ctor_set(v___x_2339_, 7, v___x_2328_);
                lean_ctor_set(v___x_2339_, 8, v___x_2328_);
                lean_ctor_set(v___x_2339_, 9, v___x_2328_);
                v___x_2340_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__5_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2341_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1___closed__6_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
                v___x_2342_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_2342_, 0, v___x_2339_);
                lean_ctor_set(v___x_2342_, 1, v___x_2340_);
                lean_ctor_set(v___x_2342_, 2, v___x_2317_);
                lean_ctor_set(v___x_2342_, 3, v___x_2333_);
                lean_ctor_set(v___x_2342_, 4, v___x_2341_);
                v___x_2343_ = lean_st_mk_ref(v___x_2342_);
                v___x_2355_ = 0;
                v___x_2356_ = l_Lean_instBEqAttributeKind_beq(v_kind_2321_, v___x_2355_);
                if v___x_2356_ == 0 {
                    lean_dec(v_decl_2319_);
                    v___x_2357_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v___x_2318_, v_kind_2321_, v___x_2338_, v___x_2343_, v___y_2322_, v___y_2323_);
                    lean_dec_ref_known(v___x_2338_, 7);
                    v___y_2345_ = v___x_2357_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_2318_);
                    v___x_2358_ = lean_box(0);
                    v___x_2359_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v_decl_2319_, v___x_2358_, v___x_2338_, v___x_2343_, v___y_2322_, v___y_2323_);
                    lean_dec_ref_known(v___x_2338_, 7);
                    v___y_2345_ = v___x_2359_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v___y_2345_) == 0 {
                    v_a_2346_ = lean_ctor_get(v___y_2345_, 0);
                    v_isSharedCheck_2354_ = (!lean_is_exclusive(v___y_2345_)) as u8;
                    if v_isSharedCheck_2354_ == 0 {
                        v___x_2348_ = v___y_2345_;
                        v_isShared_2349_ = v_isSharedCheck_2354_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2346_);
                        lean_dec(v___y_2345_);
                        v___x_2348_ = lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2354_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2343_);
                    return v___y_2345_;
                }
            }
            2 => {
                v___x_2350_ = lean_st_ref_get(v___x_2343_);
                lean_dec(v___x_2343_);
                lean_dec(v___x_2350_);
                if v_isShared_2349_ == 0 {
                    v___x_2352_ = v___x_2348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2346_);
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
    mut v___x_2360_: *mut LeanObject,
    mut v___x_2361_: *mut LeanObject,
    mut v___x_2362_: *mut LeanObject,
    mut v_decl_2363_: *mut LeanObject,
    mut v___stx_2364_: *mut LeanObject,
    mut v_kind_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2369_: u8 = 0;
    let mut v_res_2370_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2369_ = (lean_unbox(v_kind_2365_) as u8);
    v_res_2370_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_2360_, v___x_2361_, v___x_2362_, v_decl_2363_, v___stx_2364_, v_kind_boxed_2369_, v___y_2366_, v___y_2367_);
    lean_dec(v___y_2367_);
    lean_dec_ref(v___y_2366_);
    lean_dec(v___stx_2364_);
    return v_res_2370_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(
    mut v_msgData_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_st_ref_get(v___y_2373_);
    v_env_2376_ = lean_ctor_get(v___x_2375_, 0);
    lean_inc_ref(v_env_2376_);
    lean_dec(v___x_2375_);
    v_options_2377_ = lean_ctor_get(v___y_2372_, 2);
    v___x_2378_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__2);
    v___x_2379_ = lean_unsigned_to_nat(32);
    v___x_2380_ = lean_mk_empty_array_with_capacity(v___x_2379_);
    lean_dec_ref(v___x_2380_);
    v___x_2381_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_registerCoercion_spec__0_spec__0_spec__1_spec__5_spec__7_spec__8_spec__9___redArg___closed__5);
    lean_inc_ref(v_options_2377_);
    v___x_2382_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2382_, 0, v_env_2376_);
    lean_ctor_set(v___x_2382_, 1, v___x_2378_);
    lean_ctor_set(v___x_2382_, 2, v___x_2381_);
    lean_ctor_set(v___x_2382_, 3, v_options_2377_);
    v___x_2383_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2383_, 0, v___x_2382_);
    lean_ctor_set(v___x_2383_, 1, v_msgData_2371_);
    v___x_2384_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2384_, 0, v___x_2383_);
    return v___x_2384_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_msgData_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_res_2389_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msgData_2385_, v___y_2386_, v___y_2387_);
    lean_dec(v___y_2387_);
    lean_dec_ref(v___y_2386_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(
    mut v_msg_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2399_: u8 = 0;
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2404_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2394_ = lean_ctor_get(v___y_2391_, 5);
                v___x_2395_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0_spec__0(v_msg_2390_, v___y_2391_, v___y_2392_);
                v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
                v_isSharedCheck_2404_ = (!lean_is_exclusive(v___x_2395_)) as u8;
                if v_isSharedCheck_2404_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    v_isShared_2399_ = v_isSharedCheck_2404_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2396_);
                    lean_dec(v___x_2395_);
                    v___x_2398_ = lean_box(0);
                    v_isShared_2399_ = v_isSharedCheck_2404_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2394_);
                v___x_2400_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2400_, 0, v_ref_2394_);
                lean_ctor_set(v___x_2400_, 1, v_a_2396_);
                if v_isShared_2399_ == 0 {
                    lean_ctor_set_tag(v___x_2398_, 1);
                    lean_ctor_set(v___x_2398_, 0, v___x_2400_);
                    v___x_2402_ = v___x_2398_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2400_);
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
    mut v_msg_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2409_: *mut LeanObject = core::ptr::null_mut();
    v_res_2409_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_2405_, v___y_2406_, v___y_2407_);
    lean_dec(v___y_2407_);
    lean_dec_ref(v___y_2406_);
    return v_res_2409_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2412_ = l_Lean_stringToMessageData(v___x_2411_);
    return v___x_2412_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2414_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2415_ = l_Lean_stringToMessageData(v___x_2414_);
    return v___x_2415_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(
    mut v___x_2416_: *mut LeanObject,
    mut v_decl_2417_: *mut LeanObject,
    mut v___y_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2422_ = l_Lean_MessageData_ofName(v___x_2416_);
    v___x_2423_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2423_, 0, v___x_2421_);
    lean_ctor_set(v___x_2423_, 1, v___x_2422_);
    v___x_2424_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2425_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_2425_, 0, v___x_2423_);
    lean_ctor_set(v___x_2425_, 1, v___x_2424_);
    v___x_2426_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v___x_2425_, v___y_2418_, v___y_2419_);
    return v___x_2426_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v___x_2427_: *mut LeanObject,
    mut v_decl_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
    mut v___y_2430_: *mut LeanObject,
    mut v___y_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2432_: *mut LeanObject = core::ptr::null_mut();
    v_res_2432_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_(v___x_2427_, v_decl_2428_, v___y_2429_, v___y_2430_);
    lean_dec(v___y_2430_);
    lean_dec_ref(v___y_2429_);
    lean_dec(v_decl_2428_);
    return v_res_2432_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    v___x_2473_ = lean_unsigned_to_nat(3842861879);
    v___x_2474_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2475_ = l_Lean_Name_num___override(v___x_2474_, v___x_2473_);
    return v___x_2475_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2478_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2479_ = l_Lean_Name_str___override(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2481_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2482_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2483_ = l_Lean_Name_str___override(v___x_2482_, v___x_2481_);
    return v___x_2483_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = lean_unsigned_to_nat(2);
    v___x_2485_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2486_ = l_Lean_Name_num___override(v___x_2485_, v___x_2484_);
    return v___x_2486_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2496_ = 0;
    v___x_2497_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2498_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2499_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2500_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_2500_, 0, v___x_2499_);
    lean_ctor_set(v___x_2500_, 1, v___x_2498_);
    lean_ctor_set(v___x_2500_, 2, v___x_2497_);
    lean_ctor_set_uint8(
        v___x_2500_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_2496_,
    );
    return v___x_2500_;
}
pub unsafe fn _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    v___f_2501_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___f_2502_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_;
    v___x_2503_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__26_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2504_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2504_, 0, v___x_2503_);
    lean_ctor_set(v___x_2504_, 1, v___f_2502_);
    lean_ctor_set(v___x_2504_, 2, v___f_2501_);
    return v___x_2504_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    v___x_2506_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_);
    v___x_2507_ = l_Lean_registerBuiltinAttribute(v___x_2506_);
    return v___x_2507_;
}
pub unsafe fn l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2____boxed(
    mut v_a_2508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2509_: *mut LeanObject = core::ptr::null_mut();
    v_res_2509_ = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
    return v_res_2509_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_2510_: *mut LeanObject,
    mut v_msg_2511_: *mut LeanObject,
    mut v___y_2512_: *mut LeanObject,
    mut v___y_2513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    v___x_2515_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___redArg(v_msg_2511_, v___y_2512_, v___y_2513_);
    return v___x_2515_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_2516_: *mut LeanObject,
    mut v_msg_2517_: *mut LeanObject,
    mut v___y_2518_: *mut LeanObject,
    mut v___y_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2521_: *mut LeanObject = core::ptr::null_mut();
    v_res_2521_ = l_Lean_throwError___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__0(v_00_u03b1_2516_, v_msg_2517_, v___y_2518_, v___y_2519_);
    lean_dec(v___y_2519_);
    lean_dec_ref(v___y_2518_);
    return v_res_2521_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_2522_: *mut LeanObject,
    mut v_name_2523_: *mut LeanObject,
    mut v_kind_2524_: u8,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___redArg(v_name_2523_, v_kind_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_2531_: *mut LeanObject,
    mut v_name_2532_: *mut LeanObject,
    mut v_kind_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
    mut v___y_2536_: *mut LeanObject,
    mut v___y_2537_: *mut LeanObject,
    mut v___y_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kind_boxed_2539_: u8 = 0;
    let mut v_res_2540_: *mut LeanObject = core::ptr::null_mut();
    v_kind_boxed_2539_ = (lean_unbox(v_kind_2533_) as u8);
    v_res_2540_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2__spec__1(v_00_u03b1_2531_, v_name_2532_, v_kind_boxed_2539_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
    lean_dec(v___y_2537_);
    lean_dec_ref(v___y_2536_);
    lean_dec(v___y_2535_);
    lean_dec_ref(v___y_2534_);
    return v_res_2540_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_instInhabitedCoeFnType_default = _init_l_Lean_Meta_instInhabitedCoeFnType_default();
    l_Lean_Meta_instInhabitedCoeFnType = _init_l_Lean_Meta_instInhabitedCoeFnType();
    l_Lean_Meta_instToExprCoeFnType = _init_l_Lean_Meta_instToExprCoeFnType();
    lean_mark_persistent(l_Lean_Meta_instToExprCoeFnType);
    l_Lean_Meta_instToExprCoeFnInfo = _init_l_Lean_Meta_instToExprCoeFnInfo();
    lean_mark_persistent(l_Lean_Meta_instToExprCoeFnInfo);
    res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_477343235____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_coeExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_coeExt);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_CoeAttr_0__Lean_Meta_initFn_00___x40_Lean_Meta_CoeAttr_3842861879____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CoeAttr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_FunInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CoeAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_CoeAttr(builtin);
}
