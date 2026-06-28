// Lean compiler output
// Module: Lean.ErrorExplanation
// Imports: Lean.Message Lean.EnvExtension Lean.DocString.Links Lean.Message
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Array::QSort::Basic::l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::DocString::Links::{
    initialize_Lean_DocString_Links, runtime_initialize_Lean_DocString_Links,
};
use crate::r#gen::Lean::EnvExtension::{
    initialize_Lean_EnvExtension, l_Lean_SimplePersistentEnvExtension_getState___redArg,
    l_Lean_registerSimplePersistentEnvExtension___redArg, runtime_initialize_Lean_EnvExtension,
};
use crate::r#gen::Lean::Message::{
    initialize_Lean_Message, l_Lean_MessageSeverity_toString,
    l_Lean_instFromJsonMessageSeverity_fromJson, l_Lean_instToJsonMessageSeverity_toJson,
    meta_initialize_Lean_Message, runtime_initialize_Lean_Message,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_foldl___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_uget_borrowed,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_dec_lt;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 117, 109, 109, 97, 114, 121, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value:
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
        69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [77, 101, 116, 97, 100, 97, 116, 97, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value)
        as *mut LeanObject;
static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__2_value)
            as *mut LeanObject,
        18239673213070638308 as *mut LeanObject,
    ],
};
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__3_value)
            as *mut LeanObject,
        16597581185784988388 as *mut LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0_value)
            as *mut LeanObject,
        5777670751414481270 as *mut LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [115, 105, 110, 99, 101, 86, 101, 114, 115, 105, 111, 110, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13_value
        ) as *mut LeanObject,
        8223184013717887766 as *mut LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 101, 118, 101, 114, 105, 116, 121, 0],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18_value
        ) as *mut LeanObject,
        2558814583289894876 as *mut LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        114, 101, 109, 111, 118, 101, 100, 86, 101, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value:
    LeanStringObject<16> = LeanStringObject {
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
        114, 101, 109, 111, 118, 101, 100, 86, 101, 114, 115, 105, 111, 110, 63, 0,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__24_value
        ) as *mut LeanObject,
        13911480044048867773 as *mut LeanObject,
    ],
};
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25_value)
        as *mut LeanObject;
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_ErrorExplanation_instFromJsonMetadata: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_ErrorExplanation_instToJsonMetadata_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_ErrorExplanation_instToJsonMetadata___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_ErrorExplanation_instToJsonMetadata: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_instToJsonMetadata___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value: LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Lean_ErrorExplanation_summaryWithSeverity___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_summaryWithSeverity___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value: LeanStringObject<3> =
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
        m_data: [41, 32, 0],
    };
static mut l_Lean_ErrorExplanation_summaryWithSeverity___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_ErrorExplanation_summaryWithSeverity___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 69, 120, 116, 0]};
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__1_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__3_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject,18446158502798500228 as *mut LeanObject] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value: LeanCtorObject<7> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*7 + 0) as u16, other: 7, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__4_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_getErrorExplanations___redArg___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_getErrorExplanations___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_getErrorExplanations___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getErrorExplanations___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_getErrorExplanations___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_getErrorExplanations___redArg___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_getErrorExplanations___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_getErrorExplanations___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(
    mut v_j_682_: *mut LeanObject,
    mut v_k_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut LeanObject = core::ptr::null_mut();
    v___x_684_ = l_Lean_Json_getObjValD(v_j_682_, v_k_683_);
    v___x_685_ = l_Lean_Json_getStr_x3f(v___x_684_);
    return v___x_685_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0___boxed(
    mut v_j_686_: *mut LeanObject,
    mut v_k_687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_688_: *mut LeanObject = core::ptr::null_mut();
    v_res_688_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_j_686_, v_k_687_);
    lean_dec_ref(v_k_687_);
    return v_res_688_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(
    mut v_j_689_: *mut LeanObject,
    mut v_k_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    v___x_691_ = l_Lean_Json_getObjValD(v_j_689_, v_k_690_);
    v___x_692_ = l_Lean_instFromJsonMessageSeverity_fromJson(v___x_691_);
    return v___x_692_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1___boxed(
    mut v_j_693_: *mut LeanObject,
    mut v_k_694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_695_: *mut LeanObject = core::ptr::null_mut();
    v_res_695_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_j_693_, v_k_694_);
    lean_dec_ref(v_k_694_);
    return v_res_695_;
}
pub unsafe fn l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(
    mut v_x_698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_704_: u8 = 0;
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_698_) == 0 {
                    v___x_699_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2___closed__0;
                    return v___x_699_;
                } else {
                    v___x_700_ = l_Lean_Json_getStr_x3f(v_x_698_);
                    if lean_obj_tag(v___x_700_) == 0 {
                        v_a_701_ = lean_ctor_get(v___x_700_, 0);
                        v_isSharedCheck_708_ = (!lean_is_exclusive(v___x_700_)) as u8;
                        if v_isSharedCheck_708_ == 0 {
                            v___x_703_ = v___x_700_;
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_701_);
                            lean_dec(v___x_700_);
                            v___x_703_ = lean_box(0);
                            v_isShared_704_ = v_isSharedCheck_708_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_709_ = lean_ctor_get(v___x_700_, 0);
                        v_isSharedCheck_717_ = (!lean_is_exclusive(v___x_700_)) as u8;
                        if v_isSharedCheck_717_ == 0 {
                            v___x_711_ = v___x_700_;
                            v_isShared_712_ = v_isSharedCheck_717_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_709_);
                            lean_dec(v___x_700_);
                            v___x_711_ = lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_717_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_704_ == 0 {
                    v___x_706_ = v___x_703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v_a_701_);
                    v___x_706_ = v_reuseFailAlloc_707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_706_;
            }
            3 => {
                v___x_713_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_713_, 0, v_a_709_);
                if v_isShared_712_ == 0 {
                    lean_ctor_set(v___x_711_, 0, v___x_713_);
                    v___x_715_ = v___x_711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
                    v___x_715_ = v_reuseFailAlloc_716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(
    mut v_j_718_: *mut LeanObject,
    mut v_k_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Lean_Json_getObjValD(v_j_718_, v_k_719_);
    v___x_721_ = l_Option_fromJson_x3f___at___00Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2_spec__2(v___x_720_);
    return v___x_721_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2___boxed(
    mut v_j_722_: *mut LeanObject,
    mut v_k_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_j_722_, v_k_723_);
    lean_dec_ref(v_k_723_);
    return v_res_724_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5()
-> *mut LeanObject {
    let mut v___x_733_: u8 = 0;
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_733_ = 1;
    v___x_734_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__4;
    v___x_735_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_734_, v___x_733_);
    return v___x_735_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7()
-> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__6;
    v___x_738_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__5,
    );
    v___x_739_ = lean_string_append(v___x_738_, v___x_737_);
    return v___x_739_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9()
-> *mut LeanObject {
    let mut v___x_742_: u8 = 0;
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = 1;
    v___x_743_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__8;
    v___x_744_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_743_, v___x_742_);
    return v___x_744_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10()
-> *mut LeanObject {
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    v___x_745_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__9,
    );
    v___x_746_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_747_ = lean_string_append(v___x_746_, v___x_745_);
    return v___x_747_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12()
-> *mut LeanObject {
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_750_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__10,
    );
    v___x_751_ = lean_string_append(v___x_750_, v___x_749_);
    return v___x_751_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15()
-> *mut LeanObject {
    let mut v___x_755_: u8 = 0;
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    v___x_755_ = 1;
    v___x_756_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__14;
    v___x_757_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_756_, v___x_755_);
    return v___x_757_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16()
-> *mut LeanObject {
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    v___x_758_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__15,
    );
    v___x_759_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_760_ = lean_string_append(v___x_759_, v___x_758_);
    return v___x_760_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17()
-> *mut LeanObject {
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    v___x_761_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_762_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__16,
    );
    v___x_763_ = lean_string_append(v___x_762_, v___x_761_);
    return v___x_763_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20()
-> *mut LeanObject {
    let mut v___x_767_: u8 = 0;
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    v___x_767_ = 1;
    v___x_768_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__19;
    v___x_769_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_768_, v___x_767_);
    return v___x_769_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21()
-> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__20,
    );
    v___x_771_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_772_ = lean_string_append(v___x_771_, v___x_770_);
    return v___x_772_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22()
-> *mut LeanObject {
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    v___x_773_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_774_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__21,
    );
    v___x_775_ = lean_string_append(v___x_774_, v___x_773_);
    return v___x_775_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26()
-> *mut LeanObject {
    let mut v___x_780_: u8 = 0;
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    v___x_780_ = 1;
    v___x_781_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__25;
    v___x_782_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_781_, v___x_780_);
    return v___x_782_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27()
-> *mut LeanObject {
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v___x_783_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__26,
    );
    v___x_784_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__7,
    );
    v___x_785_ = lean_string_append(v___x_784_, v___x_783_);
    return v___x_785_;
}
pub unsafe fn _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28()
-> *mut LeanObject {
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_786_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__11;
    v___x_787_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27),
        core::ptr::addr_of_mut!(
            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27_once
        ),
        _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__27,
    );
    v___x_788_ = lean_string_append(v___x_787_, v___x_786_);
    return v___x_788_;
}
pub unsafe fn l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson(
    mut v_json_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_801_: u8 = 0;
    let mut v_a_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_805_: u8 = 0;
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_809_: u8 = 0;
    let mut v_a_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_822_: u8 = 0;
    let mut v_a_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut v_a_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_843_: u8 = 0;
    let mut v_a_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_851_: u8 = 0;
    let mut v_a_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v_a_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_882_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_790_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
                lean_inc(v_json_789_);
                v___x_791_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_789_, v___x_790_);
                if lean_obj_tag(v___x_791_) == 0 {
                    lean_dec(v_json_789_);
                    v_a_792_ = lean_ctor_get(v___x_791_, 0);
                    v_isSharedCheck_801_ = (!lean_is_exclusive(v___x_791_)) as u8;
                    if v_isSharedCheck_801_ == 0 {
                        v___x_794_ = v___x_791_;
                        v_isShared_795_ = v_isSharedCheck_801_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_792_);
                        lean_dec(v___x_791_);
                        v___x_794_ = lean_box(0);
                        v_isShared_795_ = v_isSharedCheck_801_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v___x_791_) == 0 {
                        lean_dec(v_json_789_);
                        v_a_802_ = lean_ctor_get(v___x_791_, 0);
                        v_isSharedCheck_809_ = (!lean_is_exclusive(v___x_791_)) as u8;
                        if v_isSharedCheck_809_ == 0 {
                            v___x_804_ = v___x_791_;
                            v_isShared_805_ = v_isSharedCheck_809_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_802_);
                            lean_dec(v___x_791_);
                            v___x_804_ = lean_box(0);
                            v_isShared_805_ = v_isSharedCheck_809_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_810_ = lean_ctor_get(v___x_791_, 0);
                        lean_inc(v_a_810_);
                        lean_dec_ref_known(v___x_791_, 1);
                        v___x_811_ =
                            l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
                        lean_inc(v_json_789_);
                        v___x_812_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__0(v_json_789_, v___x_811_);
                        if lean_obj_tag(v___x_812_) == 0 {
                            lean_dec(v_a_810_);
                            lean_dec(v_json_789_);
                            v_a_813_ = lean_ctor_get(v___x_812_, 0);
                            v_isSharedCheck_822_ = (!lean_is_exclusive(v___x_812_)) as u8;
                            if v_isSharedCheck_822_ == 0 {
                                v___x_815_ = v___x_812_;
                                v_isShared_816_ = v_isSharedCheck_822_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_813_);
                                lean_dec(v___x_812_);
                                v___x_815_ = lean_box(0);
                                v_isShared_816_ = v_isSharedCheck_822_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_812_) == 0 {
                                lean_dec(v_a_810_);
                                lean_dec(v_json_789_);
                                v_a_823_ = lean_ctor_get(v___x_812_, 0);
                                v_isSharedCheck_830_ = (!lean_is_exclusive(v___x_812_)) as u8;
                                if v_isSharedCheck_830_ == 0 {
                                    v___x_825_ = v___x_812_;
                                    v_isShared_826_ = v_isSharedCheck_830_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_823_);
                                    lean_dec(v___x_812_);
                                    v___x_825_ = lean_box(0);
                                    v_isShared_826_ = v_isSharedCheck_830_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_831_ = lean_ctor_get(v___x_812_, 0);
                                lean_inc(v_a_831_);
                                lean_dec_ref_known(v___x_812_, 1);
                                v___x_832_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
                                lean_inc(v_json_789_);
                                v___x_833_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__1(v_json_789_, v___x_832_);
                                if lean_obj_tag(v___x_833_) == 0 {
                                    lean_dec(v_a_831_);
                                    lean_dec(v_a_810_);
                                    lean_dec(v_json_789_);
                                    v_a_834_ = lean_ctor_get(v___x_833_, 0);
                                    v_isSharedCheck_843_ = (!lean_is_exclusive(v___x_833_)) as u8;
                                    if v_isSharedCheck_843_ == 0 {
                                        v___x_836_ = v___x_833_;
                                        v_isShared_837_ = v_isSharedCheck_843_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_834_);
                                        lean_dec(v___x_833_);
                                        v___x_836_ = lean_box(0);
                                        v_isShared_837_ = v_isSharedCheck_843_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    if lean_obj_tag(v___x_833_) == 0 {
                                        lean_dec(v_a_831_);
                                        lean_dec(v_a_810_);
                                        lean_dec(v_json_789_);
                                        v_a_844_ = lean_ctor_get(v___x_833_, 0);
                                        v_isSharedCheck_851_ =
                                            (!lean_is_exclusive(v___x_833_)) as u8;
                                        if v_isSharedCheck_851_ == 0 {
                                            v___x_846_ = v___x_833_;
                                            v_isShared_847_ = v_isSharedCheck_851_;
                                            state = 11;
                                            continue;
                                        } else {
                                            lean_inc(v_a_844_);
                                            lean_dec(v___x_833_);
                                            v___x_846_ = lean_box(0);
                                            v_isShared_847_ = v_isSharedCheck_851_;
                                            state = 11;
                                            continue;
                                        }
                                    } else {
                                        v_a_852_ = lean_ctor_get(v___x_833_, 0);
                                        lean_inc(v_a_852_);
                                        lean_dec_ref_known(v___x_833_, 1);
                                        v___x_853_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
                                        v___x_854_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_ErrorExplanation_instFromJsonMetadata_fromJson_spec__2(v_json_789_, v___x_853_);
                                        if lean_obj_tag(v___x_854_) == 0 {
                                            lean_dec(v_a_852_);
                                            lean_dec(v_a_831_);
                                            lean_dec(v_a_810_);
                                            v_a_855_ = lean_ctor_get(v___x_854_, 0);
                                            v_isSharedCheck_864_ =
                                                (!lean_is_exclusive(v___x_854_)) as u8;
                                            if v_isSharedCheck_864_ == 0 {
                                                v___x_857_ = v___x_854_;
                                                v_isShared_858_ = v_isSharedCheck_864_;
                                                state = 13;
                                                continue;
                                            } else {
                                                lean_inc(v_a_855_);
                                                lean_dec(v___x_854_);
                                                v___x_857_ = lean_box(0);
                                                v_isShared_858_ = v_isSharedCheck_864_;
                                                state = 13;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_854_) == 0 {
                                                lean_dec(v_a_852_);
                                                lean_dec(v_a_831_);
                                                lean_dec(v_a_810_);
                                                v_a_865_ = lean_ctor_get(v___x_854_, 0);
                                                v_isSharedCheck_872_ =
                                                    (!lean_is_exclusive(v___x_854_)) as u8;
                                                if v_isSharedCheck_872_ == 0 {
                                                    v___x_867_ = v___x_854_;
                                                    v_isShared_868_ = v_isSharedCheck_872_;
                                                    state = 15;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_865_);
                                                    lean_dec(v___x_854_);
                                                    v___x_867_ = lean_box(0);
                                                    v_isShared_868_ = v_isSharedCheck_872_;
                                                    state = 15;
                                                    continue;
                                                }
                                            } else {
                                                v_a_873_ = lean_ctor_get(v___x_854_, 0);
                                                v_isSharedCheck_882_ =
                                                    (!lean_is_exclusive(v___x_854_)) as u8;
                                                if v_isSharedCheck_882_ == 0 {
                                                    v___x_875_ = v___x_854_;
                                                    v_isShared_876_ = v_isSharedCheck_882_;
                                                    state = 17;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_873_);
                                                    lean_dec(v___x_854_);
                                                    v___x_875_ = lean_box(0);
                                                    v_isShared_876_ = v_isSharedCheck_882_;
                                                    state = 17;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_796_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__12,
                );
                v___x_797_ = lean_string_append(v___x_796_, v_a_792_);
                lean_dec(v_a_792_);
                if v_isShared_795_ == 0 {
                    lean_ctor_set(v___x_794_, 0, v___x_797_);
                    v___x_799_ = v___x_794_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_800_, 0, v___x_797_);
                    v___x_799_ = v_reuseFailAlloc_800_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_799_;
            }
            3 => {
                if v_isShared_805_ == 0 {
                    lean_ctor_set_tag(v___x_804_, 0);
                    v___x_807_ = v___x_804_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_808_, 0, v_a_802_);
                    v___x_807_ = v_reuseFailAlloc_808_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_807_;
            }
            5 => {
                v___x_817_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__17,
                );
                v___x_818_ = lean_string_append(v___x_817_, v_a_813_);
                lean_dec(v_a_813_);
                if v_isShared_816_ == 0 {
                    lean_ctor_set(v___x_815_, 0, v___x_818_);
                    v___x_820_ = v___x_815_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
                    v___x_820_ = v_reuseFailAlloc_821_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_820_;
            }
            7 => {
                if v_isShared_826_ == 0 {
                    lean_ctor_set_tag(v___x_825_, 0);
                    v___x_828_ = v___x_825_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
                    v___x_828_ = v_reuseFailAlloc_829_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_828_;
            }
            9 => {
                v___x_838_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__22,
                );
                v___x_839_ = lean_string_append(v___x_838_, v_a_834_);
                lean_dec(v_a_834_);
                if v_isShared_837_ == 0 {
                    lean_ctor_set(v___x_836_, 0, v___x_839_);
                    v___x_841_ = v___x_836_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_842_, 0, v___x_839_);
                    v___x_841_ = v_reuseFailAlloc_842_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_841_;
            }
            11 => {
                if v_isShared_847_ == 0 {
                    lean_ctor_set_tag(v___x_846_, 0);
                    v___x_849_ = v___x_846_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_850_, 0, v_a_844_);
                    v___x_849_ = v_reuseFailAlloc_850_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_849_;
            }
            13 => {
                v___x_859_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28_once
                    ),
                    _init_l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__28,
                );
                v___x_860_ = lean_string_append(v___x_859_, v_a_855_);
                lean_dec(v_a_855_);
                if v_isShared_858_ == 0 {
                    lean_ctor_set(v___x_857_, 0, v___x_860_);
                    v___x_862_ = v___x_857_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_862_;
            }
            15 => {
                if v_isShared_868_ == 0 {
                    lean_ctor_set_tag(v___x_867_, 0);
                    v___x_870_ = v___x_867_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
                    v___x_870_ = v_reuseFailAlloc_871_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_870_;
            }
            17 => {
                v___x_877_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_877_, 0, v_a_810_);
                lean_ctor_set(v___x_877_, 1, v_a_831_);
                lean_ctor_set(v___x_877_, 2, v_a_873_);
                v___x_878_ = (lean_unbox(v_a_852_) as u8);
                lean_dec(v_a_852_);
                lean_ctor_set_uint8(
                    v___x_877_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_878_,
                );
                if v_isShared_876_ == 0 {
                    lean_ctor_set(v___x_875_, 0, v___x_877_);
                    v___x_880_ = v___x_875_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_877_);
                    v___x_880_ = v_reuseFailAlloc_881_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_880_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(
    mut v_k_885_: *mut LeanObject,
    mut v_x_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_886_) == 0 {
                    lean_dec_ref(v_k_885_);
                    v___x_887_ = lean_box(0);
                    return v___x_887_;
                } else {
                    v_val_888_ = lean_ctor_get(v_x_886_, 0);
                    v_isSharedCheck_898_ = (!lean_is_exclusive(v_x_886_)) as u8;
                    if v_isSharedCheck_898_ == 0 {
                        v___x_890_ = v_x_886_;
                        v_isShared_891_ = v_isSharedCheck_898_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_888_);
                        lean_dec(v_x_886_);
                        v___x_890_ = lean_box(0);
                        v_isShared_891_ = v_isSharedCheck_898_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_891_ == 0 {
                    lean_ctor_set_tag(v___x_890_, 3);
                    v___x_893_ = v___x_890_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_897_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_897_, 0, v_val_888_);
                    v___x_893_ = v_reuseFailAlloc_897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_894_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_894_, 0, v_k_885_);
                lean_ctor_set(v___x_894_, 1, v___x_893_);
                v___x_895_ = lean_box(0);
                v___x_896_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_896_, 0, v___x_894_);
                lean_ctor_set(v___x_896_, 1, v___x_895_);
                return v___x_896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_899_) == 0 {
                    v___x_901_ = lean_array_to_list(v_a_900_);
                    return v___x_901_;
                } else {
                    v_head_902_ = lean_ctor_get(v_a_899_, 0);
                    lean_inc(v_head_902_);
                    v_tail_903_ = lean_ctor_get(v_a_899_, 1);
                    lean_inc(v_tail_903_);
                    lean_dec_ref_known(v_a_899_, 2);
                    v___x_904_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_900_,
                        v_head_902_,
                    );
                    v_a_899_ = v_tail_903_;
                    v_a_900_ = v___x_904_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ErrorExplanation_instToJsonMetadata_toJson(
    mut v_x_908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_summary_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sinceVersion_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_911_: u8 = 0;
    let mut v_removedVersion_x3f_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v_summary_909_ = lean_ctor_get(v_x_908_, 0);
    lean_inc_ref(v_summary_909_);
    v_sinceVersion_910_ = lean_ctor_get(v_x_908_, 1);
    lean_inc_ref(v_sinceVersion_910_);
    v_severity_911_ = lean_ctor_get_uint8(
        v_x_908_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v_removedVersion_x3f_912_ = lean_ctor_get(v_x_908_, 2);
    lean_inc(v_removedVersion_x3f_912_);
    lean_dec_ref(v_x_908_);
    v___x_913_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__0;
    v___x_914_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v_summary_909_);
    v___x_915_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_915_, 0, v___x_913_);
    lean_ctor_set(v___x_915_, 1, v___x_914_);
    v___x_916_ = lean_box(0);
    v___x_917_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_917_, 0, v___x_915_);
    lean_ctor_set(v___x_917_, 1, v___x_916_);
    v___x_918_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__13;
    v___x_919_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_919_, 0, v_sinceVersion_910_);
    v___x_920_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_920_, 0, v___x_918_);
    lean_ctor_set(v___x_920_, 1, v___x_919_);
    v___x_921_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_921_, 0, v___x_920_);
    lean_ctor_set(v___x_921_, 1, v___x_916_);
    v___x_922_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__18;
    v___x_923_ = l_Lean_instToJsonMessageSeverity_toJson(v_severity_911_);
    v___x_924_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_924_, 0, v___x_922_);
    lean_ctor_set(v___x_924_, 1, v___x_923_);
    v___x_925_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_925_, 0, v___x_924_);
    lean_ctor_set(v___x_925_, 1, v___x_916_);
    v___x_926_ = l_Lean_ErrorExplanation_instFromJsonMetadata_fromJson___closed__23;
    v___x_927_ = l_Lean_Json_opt___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__0(
        v___x_926_,
        v_removedVersion_x3f_912_,
    );
    v___x_928_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_928_, 0, v___x_927_);
    lean_ctor_set(v___x_928_, 1, v___x_916_);
    v___x_929_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_929_, 0, v___x_925_);
    lean_ctor_set(v___x_929_, 1, v___x_928_);
    v___x_930_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_930_, 0, v___x_921_);
    lean_ctor_set(v___x_930_, 1, v___x_929_);
    v___x_931_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_931_, 0, v___x_917_);
    lean_ctor_set(v___x_931_, 1, v___x_930_);
    v___x_932_ = l_Lean_ErrorExplanation_instToJsonMetadata_toJson___closed__0;
    v___x_933_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_ErrorExplanation_instToJsonMetadata_toJson_spec__1(v___x_931_, v___x_932_);
    v___x_934_ = l_Lean_Json_mkObj(v___x_933_);
    lean_dec(v___x_933_);
    return v___x_934_;
}
pub unsafe fn l_Lean_ErrorExplanation_summaryWithSeverity(
    mut v_explan_939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_metadata_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_summary_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_severity_942_: u8 = 0;
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    v_metadata_940_ = lean_ctor_get(v_explan_939_, 1);
    v_summary_941_ = lean_ctor_get(v_metadata_940_, 0);
    v_severity_942_ = lean_ctor_get_uint8(
        v_metadata_940_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v___x_943_ = l_Lean_ErrorExplanation_summaryWithSeverity___closed__0;
    v___x_944_ = l_Lean_MessageSeverity_toString(v_severity_942_);
    v___x_945_ = lean_string_append(v___x_943_, v___x_944_);
    lean_dec_ref(v___x_944_);
    v___x_946_ = l_Lean_ErrorExplanation_summaryWithSeverity___closed__1;
    v___x_947_ = lean_string_append(v___x_945_, v___x_946_);
    v___x_948_ = lean_string_append(v___x_947_, v_summary_941_);
    return v___x_948_;
}
pub unsafe fn l_Lean_ErrorExplanation_summaryWithSeverity___boxed(
    mut v_explan_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_950_: *mut LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lean_ErrorExplanation_summaryWithSeverity(v_explan_949_);
    lean_dec_ref(v_explan_949_);
    return v_res_950_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__0_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_s_951_: *mut LeanObject,
    mut v_x_952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    v_fst_953_ = lean_ctor_get(v_x_952_, 0);
    lean_inc(v_fst_953_);
    v_snd_954_ = lean_ctor_get(v_x_952_, 1);
    lean_inc(v_snd_954_);
    lean_dec_ref(v_x_952_);
    v___x_955_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
        v_fst_953_, v_snd_954_, v_s_951_,
    );
    return v___x_955_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(
    mut v_as_956_: *mut LeanObject,
    mut v_i_957_: usize,
    mut v_stop_958_: usize,
    mut v_b_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_960_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: usize = 0;
    let mut v___x_966_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_960_ = lean_usize_dec_eq(v_i_957_, v_stop_958_);
                if v___x_960_ == 0 {
                    v___x_961_ = lean_array_uget_borrowed(v_as_956_, v_i_957_);
                    v_fst_962_ = lean_ctor_get(v___x_961_, 0);
                    v_snd_963_ = lean_ctor_get(v___x_961_, 1);
                    lean_inc(v_snd_963_);
                    lean_inc(v_fst_962_);
                    v___x_964_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_962_, v_snd_963_, v_b_959_);
                    v___x_965_ = 1usize;
                    v___x_966_ = lean_usize_add(v_i_957_, v___x_965_);
                    v_i_957_ = v___x_966_;
                    v_b_959_ = v___x_964_;
                    state = 0;
                    continue;
                } else {
                    return v_b_959_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_as_968_: *mut LeanObject,
    mut v_i_969_: *mut LeanObject,
    mut v_stop_970_: *mut LeanObject,
    mut v_b_971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_972_: usize = 0;
    let mut v_stop_boxed_973_: usize = 0;
    let mut v_res_974_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_972_ = lean_unbox_usize(v_i_969_);
    lean_dec(v_i_969_);
    v_stop_boxed_973_ = lean_unbox_usize(v_stop_970_);
    lean_dec(v_stop_970_);
    v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_968_, v_i_boxed_972_, v_stop_boxed_973_, v_b_971_);
    lean_dec_ref(v_as_968_);
    return v_res_974_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(
    mut v_as_975_: *mut LeanObject,
    mut v_i_976_: usize,
    mut v_stop_977_: usize,
    mut v_b_978_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_979_: u8 = 0;
    v___x_979_ = lean_usize_dec_eq(v_i_976_, v_stop_977_);
    if v___x_979_ == 0 {
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fst_981_: *mut LeanObject = core::ptr::null_mut();
        let mut v_snd_982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_984_: usize = 0;
        let mut v___x_985_: usize = 0;
        let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
        v___x_980_ = lean_array_uget_borrowed(v_as_975_, v_i_976_);
        v_fst_981_ = lean_ctor_get(v___x_980_, 0);
        v_snd_982_ = lean_ctor_get(v___x_980_, 1);
        lean_inc(v_snd_982_);
        lean_inc(v_fst_981_);
        v___x_983_ =
            l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                v_fst_981_, v_snd_982_, v_b_978_,
            );
        v___x_984_ = 1usize;
        v___x_985_ = lean_usize_add(v_i_976_, v___x_984_);
        v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0_spec__0(v_as_975_, v___x_985_, v_stop_977_, v___x_983_);
        return v___x_986_;
    } else {
        return v_b_978_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0___boxed(
    mut v_as_987_: *mut LeanObject,
    mut v_i_988_: *mut LeanObject,
    mut v_stop_989_: *mut LeanObject,
    mut v_b_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_991_: usize = 0;
    let mut v_stop_boxed_992_: usize = 0;
    let mut v_res_993_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_991_ = lean_unbox_usize(v_i_988_);
    lean_dec(v_i_988_);
    v_stop_boxed_992_ = lean_unbox_usize(v_stop_989_);
    lean_dec(v_stop_989_);
    v_res_993_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v_as_987_, v_i_boxed_991_, v_stop_boxed_992_, v_b_990_);
    lean_dec_ref(v_as_987_);
    return v_res_993_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(
    mut v_as_994_: *mut LeanObject,
    mut v_i_995_: usize,
    mut v_stop_996_: usize,
    mut v_b_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: usize = 0;
    let mut v___x_1001_: usize = 0;
    let mut v___x_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: u8 = 0;
    let mut v___x_1008_: u8 = 0;
    let mut v___x_1009_: usize = 0;
    let mut v___x_1010_: usize = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: usize = 0;
    let mut v___x_1013_: usize = 0;
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1003_ = lean_usize_dec_eq(v_i_995_, v_stop_996_);
                if v___x_1003_ == 0 {
                    v___x_1004_ = lean_array_uget_borrowed(v_as_994_, v_i_995_);
                    v___x_1005_ = lean_unsigned_to_nat(0);
                    v___x_1006_ = lean_array_get_size(v___x_1004_);
                    v___x_1007_ = lean_nat_dec_lt(v___x_1005_, v___x_1006_);
                    if v___x_1007_ == 0 {
                        v___y_999_ = v_b_997_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1008_ = lean_nat_dec_le(v___x_1006_, v___x_1006_);
                        if v___x_1008_ == 0 {
                            if v___x_1007_ == 0 {
                                v___y_999_ = v_b_997_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1009_ = 0usize;
                                v___x_1010_ = lean_usize_of_nat(v___x_1006_);
                                v___x_1011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_1004_, v___x_1009_, v___x_1010_, v_b_997_);
                                v___y_999_ = v___x_1011_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_1012_ = 0usize;
                            v___x_1013_ = lean_usize_of_nat(v___x_1006_);
                            v___x_1014_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__0(v___x_1004_, v___x_1012_, v___x_1013_, v_b_997_);
                            v___y_999_ = v___x_1014_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_997_;
                }
            }
            1 => {
                v___x_1000_ = 1usize;
                v___x_1001_ = lean_usize_add(v_i_995_, v___x_1000_);
                v_i_995_ = v___x_1001_;
                v_b_997_ = v___y_999_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1___boxed(
    mut v_as_1015_: *mut LeanObject,
    mut v_i_1016_: *mut LeanObject,
    mut v_stop_1017_: *mut LeanObject,
    mut v_b_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1019_: usize = 0;
    let mut v_stop_boxed_1020_: usize = 0;
    let mut v_res_1021_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1019_ = lean_unbox_usize(v_i_1016_);
    lean_dec(v_i_1016_);
    v_stop_boxed_1020_ = lean_unbox_usize(v_stop_1017_);
    lean_dec(v_stop_1017_);
    v_res_1021_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_as_1015_, v_i_boxed_1019_, v_stop_boxed_1020_, v_b_1018_);
    lean_dec_ref(v_as_1015_);
    return v_res_1021_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_ess_1022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    v___x_1023_ = lean_box(1);
    v___x_1024_ = lean_unsigned_to_nat(0);
    v___x_1025_ = lean_array_get_size(v_ess_1022_);
    v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
    if v___x_1026_ == 0 {
        return v___x_1023_;
    } else {
        let mut v___x_1027_: u8 = 0;
        v___x_1027_ = lean_nat_dec_le(v___x_1025_, v___x_1025_);
        if v___x_1027_ == 0 {
            if v___x_1026_ == 0 {
                return v___x_1023_;
            } else {
                let mut v___x_1028_: usize = 0;
                let mut v___x_1029_: usize = 0;
                let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
                v___x_1028_ = 0usize;
                v___x_1029_ = lean_usize_of_nat(v___x_1025_);
                v___x_1030_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_1022_, v___x_1028_, v___x_1029_, v___x_1023_);
                return v___x_1030_;
            }
        } else {
            let mut v___x_1031_: usize = 0;
            let mut v___x_1032_: usize = 0;
            let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
            v___x_1031_ = 0usize;
            v___x_1032_ = lean_usize_of_nat(v___x_1025_);
            v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2__spec__1(v_ess_1022_, v___x_1031_, v___x_1032_, v___x_1023_);
            return v___x_1033_;
        }
    }
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(
    mut v_ess_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1035_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__1_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(v_ess_1034_);
    lean_dec_ref(v_ess_1034_);
    return v_res_1035_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn___lam__2_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_(
    mut v_es_1036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    v___x_1037_ = lean_array_mk(v_es_1036_);
    return v___x_1037_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    v___x_1053_ = l___private_Lean_ErrorExplanation_0__Lean_initFn___closed__5_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_;
    v___x_1054_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_1053_);
    return v___x_1054_;
}
pub unsafe fn l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2____boxed(
    mut v_a_1055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1056_: *mut LeanObject = core::ptr::null_mut();
    v_res_1056_ = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
    return v_res_1056_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg___lam__0(
    mut v___x_1057_: *mut LeanObject,
    mut v_name_1058_: *mut LeanObject,
    mut v_toPure_1059_: *mut LeanObject,
    mut v_____do__lift_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
    v___x_1061_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1062_ = lean_ctor_get(v___x_1061_, 0);
    v_asyncMode_1063_ = lean_ctor_get(v_toEnvExtension_1062_, 2);
    v___x_1064_ = lean_box(0);
    v___x_1065_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1057_,
        v___x_1061_,
        v_____do__lift_1060_,
        v_asyncMode_1063_,
        v___x_1064_,
    );
    v___x_1066_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1065_,
            v_name_1058_,
        );
    lean_dec(v___x_1065_);
    v___x_1067_ = lean_apply_2(v_toPure_1059_, lean_box(0), v___x_1066_);
    return v___x_1067_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed(
    mut v___x_1068_: *mut LeanObject,
    mut v_name_1069_: *mut LeanObject,
    mut v_toPure_1070_: *mut LeanObject,
    mut v_____do__lift_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1072_: *mut LeanObject = core::ptr::null_mut();
    v_res_1072_ = l_Lean_getErrorExplanation_x3f___redArg___lam__0(
        v___x_1068_,
        v_name_1069_,
        v_toPure_1070_,
        v_____do__lift_1071_,
    );
    lean_dec(v_name_1069_);
    return v_res_1072_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___redArg(
    mut v_inst_1073_: *mut LeanObject,
    mut v_inst_1074_: *mut LeanObject,
    mut v_name_1075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1076_ = lean_ctor_get(v_inst_1073_, 0);
    lean_inc_ref(v_toApplicative_1076_);
    v_toBind_1077_ = lean_ctor_get(v_inst_1073_, 1);
    lean_inc(v_toBind_1077_);
    lean_dec_ref(v_inst_1073_);
    v_getEnv_1078_ = lean_ctor_get(v_inst_1074_, 0);
    lean_inc(v_getEnv_1078_);
    lean_dec_ref(v_inst_1074_);
    v_toPure_1079_ = lean_ctor_get(v_toApplicative_1076_, 1);
    lean_inc(v_toPure_1079_);
    lean_dec_ref(v_toApplicative_1076_);
    v___x_1080_ = lean_box(1);
    v___f_1081_ = lean_alloc_closure(
        l_Lean_getErrorExplanation_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1081_, 0, v___x_1080_);
    lean_closure_set(v___f_1081_, 1, v_name_1075_);
    lean_closure_set(v___f_1081_, 2, v_toPure_1079_);
    v___x_1082_ = lean_apply_4(
        v_toBind_1077_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1078_,
        v___f_1081_,
    );
    return v___x_1082_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f(
    mut v_m_1083_: *mut LeanObject,
    mut v_inst_1084_: *mut LeanObject,
    mut v_inst_1085_: *mut LeanObject,
    mut v_name_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_Lean_getErrorExplanation_x3f___redArg(v_inst_1084_, v_inst_1085_, v_name_1086_);
    return v___x_1087_;
}
pub unsafe fn l_Lean_getErrorExplanationRaw_x3f(
    mut v_env_1088_: *mut LeanObject,
    mut v_name_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    v___x_1090_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1091_ = lean_ctor_get(v___x_1090_, 0);
    v_asyncMode_1092_ = lean_ctor_get(v_toEnvExtension_1091_, 2);
    v___x_1093_ = lean_box(1);
    v___x_1094_ = lean_box(0);
    v___x_1095_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1093_,
        v___x_1090_,
        v_env_1088_,
        v_asyncMode_1092_,
        v___x_1094_,
    );
    v___x_1096_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_1095_,
            v_name_1089_,
        );
    lean_dec(v___x_1095_);
    return v___x_1096_;
}
pub unsafe fn l_Lean_getErrorExplanationRaw_x3f___boxed(
    mut v_env_1097_: *mut LeanObject,
    mut v_name_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1099_: *mut LeanObject = core::ptr::null_mut();
    v_res_1099_ = l_Lean_getErrorExplanationRaw_x3f(v_env_1097_, v_name_1098_);
    lean_dec(v_name_1098_);
    return v_res_1099_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg___lam__0(
    mut v___x_1100_: *mut LeanObject,
    mut v_name_1101_: *mut LeanObject,
    mut v_toPure_1102_: *mut LeanObject,
    mut v_____do__lift_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_1105_ = lean_ctor_get(v___x_1104_, 0);
    v_asyncMode_1106_ = lean_ctor_get(v_toEnvExtension_1105_, 2);
    v___x_1107_ = lean_box(0);
    v___x_1108_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_1100_,
        v___x_1104_,
        v_____do__lift_1103_,
        v_asyncMode_1106_,
        v___x_1107_,
    );
    v___x_1109_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(
            v_name_1101_,
            v___x_1108_,
        );
    lean_dec(v___x_1108_);
    v___x_1110_ = lean_box((v___x_1109_) as usize);
    v___x_1111_ = lean_apply_2(v_toPure_1102_, lean_box(0), v___x_1110_);
    return v___x_1111_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg___lam__0___boxed(
    mut v___x_1112_: *mut LeanObject,
    mut v_name_1113_: *mut LeanObject,
    mut v_toPure_1114_: *mut LeanObject,
    mut v_____do__lift_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1116_: *mut LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Lean_hasErrorExplanation___redArg___lam__0(
        v___x_1112_,
        v_name_1113_,
        v_toPure_1114_,
        v_____do__lift_1115_,
    );
    lean_dec(v_name_1113_);
    return v_res_1116_;
}
pub unsafe fn l_Lean_hasErrorExplanation___redArg(
    mut v_inst_1117_: *mut LeanObject,
    mut v_inst_1118_: *mut LeanObject,
    mut v_name_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1120_ = lean_ctor_get(v_inst_1117_, 0);
    lean_inc_ref(v_toApplicative_1120_);
    v_toBind_1121_ = lean_ctor_get(v_inst_1117_, 1);
    lean_inc(v_toBind_1121_);
    lean_dec_ref(v_inst_1117_);
    v_getEnv_1122_ = lean_ctor_get(v_inst_1118_, 0);
    lean_inc(v_getEnv_1122_);
    lean_dec_ref(v_inst_1118_);
    v_toPure_1123_ = lean_ctor_get(v_toApplicative_1120_, 1);
    lean_inc(v_toPure_1123_);
    lean_dec_ref(v_toApplicative_1120_);
    v___x_1124_ = lean_box(1);
    v___f_1125_ = lean_alloc_closure(
        l_Lean_hasErrorExplanation___redArg___lam__0___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1125_, 0, v___x_1124_);
    lean_closure_set(v___f_1125_, 1, v_name_1119_);
    lean_closure_set(v___f_1125_, 2, v_toPure_1123_);
    v___x_1126_ = lean_apply_4(
        v_toBind_1121_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1122_,
        v___f_1125_,
    );
    return v___x_1126_;
}
pub unsafe fn l_Lean_hasErrorExplanation(
    mut v_m_1127_: *mut LeanObject,
    mut v_inst_1128_: *mut LeanObject,
    mut v_inst_1129_: *mut LeanObject,
    mut v_name_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = l_Lean_hasErrorExplanation___redArg(v_inst_1128_, v_inst_1129_, v_name_1130_);
    return v___x_1131_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__0(
    mut v_e_1132_: *mut LeanObject,
    mut v_e_x27_1133_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: u8 = 0;
    v_fst_1134_ = lean_ctor_get(v_e_1132_, 0);
    lean_inc(v_fst_1134_);
    lean_dec_ref(v_e_1132_);
    v_fst_1135_ = lean_ctor_get(v_e_x27_1133_, 0);
    lean_inc(v_fst_1135_);
    lean_dec_ref(v_e_x27_1133_);
    v___x_1136_ = 1;
    v___x_1137_ = l_Lean_Name_toString(v_fst_1134_, v___x_1136_);
    v___x_1138_ = l_Lean_Name_toString(v_fst_1135_, v___x_1136_);
    v___x_1139_ = lean_string_dec_lt(v___x_1137_, v___x_1138_);
    lean_dec_ref(v___x_1138_);
    lean_dec_ref(v___x_1137_);
    return v___x_1139_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__0___boxed(
    mut v_e_1140_: *mut LeanObject,
    mut v_e_x27_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1142_: u8 = 0;
    let mut v_r_1143_: *mut LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Lean_getErrorExplanations___redArg___lam__0(v_e_1140_, v_e_x27_1141_);
    v_r_1143_ = lean_box((v_res_1142_) as usize);
    return v_r_1143_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__1(
    mut v_acc_1144_: *mut LeanObject,
    mut v_k_1145_: *mut LeanObject,
    mut v_v_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    v___x_1147_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1147_, 0, v_k_1145_);
    lean_ctor_set(v___x_1147_, 1, v_v_1146_);
    v___x_1148_ = lean_array_push(v_acc_1144_, v___x_1147_);
    return v___x_1148_;
}
pub unsafe fn l_Lean_getErrorExplanations___redArg___lam__2(
    mut v___x_1151_: *mut LeanObject,
    mut v___f_1152_: *mut LeanObject,
    mut v___f_1153_: *mut LeanObject,
    mut v_toPure_1154_: *mut LeanObject,
    mut v_____do__lift_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: u8 = 0;
    let mut v___x_1176_: u8 = 0;
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1156_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_1157_ = lean_ctor_get(v___x_1156_, 0);
                v_asyncMode_1158_ = lean_ctor_get(v_toEnvExtension_1157_, 2);
                v___x_1159_ = lean_box(0);
                v___x_1160_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1151_,
                    v___x_1156_,
                    v_____do__lift_1155_,
                    v_asyncMode_1158_,
                    v___x_1159_,
                );
                v___x_1161_ = lean_unsigned_to_nat(0);
                v___x_1162_ = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
                v___x_1163_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(
                    v___f_1152_,
                    v___x_1162_,
                    v___x_1160_,
                );
                v___x_1164_ = lean_array_get_size(v___x_1163_);
                v___x_1170_ = lean_nat_dec_eq(v___x_1164_, v___x_1161_);
                if v___x_1170_ == 0 {
                    v___x_1171_ = lean_unsigned_to_nat(1);
                    v___x_1172_ = lean_nat_sub(v___x_1164_, v___x_1171_);
                    v___x_1176_ = lean_nat_dec_le(v___x_1161_, v___x_1172_);
                    if v___x_1176_ == 0 {
                        lean_inc(v___x_1172_);
                        v___y_1174_ = v___x_1172_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1174_ = v___x_1161_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___f_1153_);
                    v___x_1177_ = lean_apply_2(v_toPure_1154_, lean_box(0), v___x_1163_);
                    return v___x_1177_;
                }
            }
            1 => {
                v___x_1168_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort(
                    lean_box(0),
                    v___f_1153_,
                    v___x_1164_,
                    v___x_1163_,
                    v___y_1166_,
                    v___y_1167_,
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                );
                lean_dec(v___y_1167_);
                v___x_1169_ = lean_apply_2(v_toPure_1154_, lean_box(0), v___x_1168_);
                return v___x_1169_;
            }
            2 => {
                v___x_1175_ = lean_nat_dec_le(v___y_1174_, v___x_1172_);
                if v___x_1175_ == 0 {
                    lean_dec(v___x_1172_);
                    lean_inc(v___y_1174_);
                    v___y_1166_ = v___y_1174_;
                    v___y_1167_ = v___y_1174_;
                    state = 1;
                    continue;
                } else {
                    v___y_1166_ = v___y_1174_;
                    v___y_1167_ = v___x_1172_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getErrorExplanations___redArg(
    mut v_inst_1180_: *mut LeanObject,
    mut v_inst_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getEnv_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1182_ = lean_ctor_get(v_inst_1180_, 0);
    lean_inc_ref(v_toApplicative_1182_);
    v_toBind_1183_ = lean_ctor_get(v_inst_1180_, 1);
    lean_inc(v_toBind_1183_);
    lean_dec_ref(v_inst_1180_);
    v_getEnv_1184_ = lean_ctor_get(v_inst_1181_, 0);
    lean_inc(v_getEnv_1184_);
    lean_dec_ref(v_inst_1181_);
    v_toPure_1185_ = lean_ctor_get(v_toApplicative_1182_, 1);
    lean_inc(v_toPure_1185_);
    lean_dec_ref(v_toApplicative_1182_);
    v___f_1186_ = l_Lean_getErrorExplanations___redArg___closed__0;
    v___f_1187_ = l_Lean_getErrorExplanations___redArg___closed__1;
    v___x_1188_ = lean_box(1);
    v___f_1189_ = lean_alloc_closure(
        l_Lean_getErrorExplanations___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1189_, 0, v___x_1188_);
    lean_closure_set(v___f_1189_, 1, v___f_1187_);
    lean_closure_set(v___f_1189_, 2, v___f_1186_);
    lean_closure_set(v___f_1189_, 3, v_toPure_1185_);
    v___x_1190_ = lean_apply_4(
        v_toBind_1183_,
        lean_box(0),
        lean_box(0),
        v_getEnv_1184_,
        v___f_1189_,
    );
    return v___x_1190_;
}
pub unsafe fn l_Lean_getErrorExplanations(
    mut v_m_1191_: *mut LeanObject,
    mut v_inst_1192_: *mut LeanObject,
    mut v_inst_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    v___x_1194_ = l_Lean_getErrorExplanations___redArg(v_inst_1192_, v_inst_1193_);
    return v___x_1194_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(
    mut v_hi_1195_: *mut LeanObject,
    mut v_pivot_1196_: *mut LeanObject,
    mut v_as_1197_: *mut LeanObject,
    mut v_i_1198_: *mut LeanObject,
    mut v_k_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1200_: u8 = 0;
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1200_ = lean_nat_dec_lt(v_k_1199_, v_hi_1195_);
                if v___x_1200_ == 0 {
                    lean_dec(v_k_1199_);
                    lean_dec_ref(v_pivot_1196_);
                    v___x_1201_ = lean_array_fswap(v_as_1197_, v_i_1198_, v_hi_1195_);
                    v___x_1202_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1202_, 0, v_i_1198_);
                    lean_ctor_set(v___x_1202_, 1, v___x_1201_);
                    return v___x_1202_;
                } else {
                    v___x_1203_ = lean_array_fget_borrowed(v_as_1197_, v_k_1199_);
                    v_fst_1204_ = lean_ctor_get(v___x_1203_, 0);
                    v_fst_1205_ = lean_ctor_get(v_pivot_1196_, 0);
                    lean_inc(v_fst_1204_);
                    v___x_1206_ = l_Lean_Name_toString(v_fst_1204_, v___x_1200_);
                    lean_inc(v_fst_1205_);
                    v___x_1207_ = l_Lean_Name_toString(v_fst_1205_, v___x_1200_);
                    v___x_1208_ = lean_string_dec_lt(v___x_1206_, v___x_1207_);
                    lean_dec_ref(v___x_1207_);
                    lean_dec_ref(v___x_1206_);
                    if v___x_1208_ == 0 {
                        v___x_1209_ = lean_unsigned_to_nat(1);
                        v___x_1210_ = lean_nat_add(v_k_1199_, v___x_1209_);
                        lean_dec(v_k_1199_);
                        v_k_1199_ = v___x_1210_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1212_ = lean_array_fswap(v_as_1197_, v_i_1198_, v_k_1199_);
                        v___x_1213_ = lean_unsigned_to_nat(1);
                        v___x_1214_ = lean_nat_add(v_i_1198_, v___x_1213_);
                        lean_dec(v_i_1198_);
                        v___x_1215_ = lean_nat_add(v_k_1199_, v___x_1213_);
                        lean_dec(v_k_1199_);
                        v_as_1197_ = v___x_1212_;
                        v_i_1198_ = v___x_1214_;
                        v_k_1199_ = v___x_1215_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg___boxed(
    mut v_hi_1217_: *mut LeanObject,
    mut v_pivot_1218_: *mut LeanObject,
    mut v_as_1219_: *mut LeanObject,
    mut v_i_1220_: *mut LeanObject,
    mut v_k_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1222_: *mut LeanObject = core::ptr::null_mut();
    v_res_1222_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1217_, v_pivot_1218_, v_as_1219_, v_i_1220_, v_k_1221_);
    lean_dec(v_hi_1217_);
    return v_res_1222_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(
    mut v___x_1223_: u8,
    mut v_e_1224_: *mut LeanObject,
    mut v_e_x27_1225_: *mut LeanObject,
) -> u8 {
    let mut v_fst_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: u8 = 0;
    v_fst_1226_ = lean_ctor_get(v_e_1224_, 0);
    lean_inc(v_fst_1226_);
    lean_dec_ref(v_e_1224_);
    v_fst_1227_ = lean_ctor_get(v_e_x27_1225_, 0);
    lean_inc(v_fst_1227_);
    lean_dec_ref(v_e_x27_1225_);
    v___x_1228_ = l_Lean_Name_toString(v_fst_1226_, v___x_1223_);
    v___x_1229_ = l_Lean_Name_toString(v_fst_1227_, v___x_1223_);
    v___x_1230_ = lean_string_dec_lt(v___x_1228_, v___x_1229_);
    lean_dec_ref(v___x_1229_);
    lean_dec_ref(v___x_1228_);
    return v___x_1230_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0___boxed(
    mut v___x_1231_: *mut LeanObject,
    mut v_e_1232_: *mut LeanObject,
    mut v_e_x27_1233_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_400__boxed_1234_: u8 = 0;
    let mut v_res_1235_: u8 = 0;
    let mut v_r_1236_: *mut LeanObject = core::ptr::null_mut();
    v___x_400__boxed_1234_ = (lean_unbox(v___x_1231_) as u8);
    v_res_1235_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_400__boxed_1234_, v_e_1232_, v_e_x27_1233_);
    v_r_1236_ = lean_box((v_res_1235_) as usize);
    return v_r_1236_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(
    mut v_n_1237_: *mut LeanObject,
    mut v_as_1238_: *mut LeanObject,
    mut v_lo_1239_: *mut LeanObject,
    mut v_hi_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: u8 = 0;
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: u8 = 0;
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1252_ = lean_nat_dec_lt(v_lo_1239_, v_hi_1240_);
                if v___x_1252_ == 0 {
                    lean_dec(v_lo_1239_);
                    return v_as_1238_;
                } else {
                    v___x_1253_ = lean_nat_add(v_lo_1239_, v_hi_1240_);
                    v___x_1254_ = lean_unsigned_to_nat(1);
                    v_mid_1255_ = lean_nat_shiftr(v___x_1253_, v___x_1254_);
                    lean_dec(v___x_1253_);
                    v___x_1268_ = lean_array_fget_borrowed(v_as_1238_, v_mid_1255_);
                    v___x_1269_ = lean_array_fget_borrowed(v_as_1238_, v_lo_1239_);
                    lean_inc(v___x_1269_);
                    lean_inc(v___x_1268_);
                    v___x_1270_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1268_, v___x_1269_);
                    if v___x_1270_ == 0 {
                        v___y_1263_ = v_as_1238_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1271_ = lean_array_fswap(v_as_1238_, v_lo_1239_, v_mid_1255_);
                        v___y_1263_ = v___x_1271_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1243_ = lean_array_fget(v___y_1242_, v_hi_1240_);
                lean_inc_n(v_lo_1239_, 2);
                v___x_1244_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1240_, v_pivot_1243_, v___y_1242_, v_lo_1239_, v_lo_1239_);
                v_fst_1245_ = lean_ctor_get(v___x_1244_, 0);
                lean_inc(v_fst_1245_);
                v_snd_1246_ = lean_ctor_get(v___x_1244_, 1);
                lean_inc(v_snd_1246_);
                lean_dec_ref(v___x_1244_);
                v___x_1247_ = lean_nat_dec_le(v_hi_1240_, v_fst_1245_);
                if v___x_1247_ == 0 {
                    v___x_1248_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1237_, v_snd_1246_, v_lo_1239_, v_fst_1245_);
                    v___x_1249_ = lean_unsigned_to_nat(1);
                    v___x_1250_ = lean_nat_add(v_fst_1245_, v___x_1249_);
                    lean_dec(v_fst_1245_);
                    v_as_1238_ = v___x_1248_;
                    v_lo_1239_ = v___x_1250_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_1245_);
                    lean_dec(v_lo_1239_);
                    return v_snd_1246_;
                }
            }
            2 => {
                v___x_1258_ = lean_array_fget_borrowed(v___y_1257_, v_mid_1255_);
                v___x_1259_ = lean_array_fget_borrowed(v___y_1257_, v_hi_1240_);
                lean_inc(v___x_1259_);
                lean_inc(v___x_1258_);
                v___x_1260_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1258_, v___x_1259_);
                if v___x_1260_ == 0 {
                    lean_dec(v_mid_1255_);
                    v___y_1242_ = v___y_1257_;
                    state = 1;
                    continue;
                } else {
                    v___x_1261_ = lean_array_fswap(v___y_1257_, v_mid_1255_, v_hi_1240_);
                    lean_dec(v_mid_1255_);
                    v___y_1242_ = v___x_1261_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1264_ = lean_array_fget_borrowed(v___y_1263_, v_hi_1240_);
                v___x_1265_ = lean_array_fget_borrowed(v___y_1263_, v_lo_1239_);
                lean_inc(v___x_1265_);
                lean_inc(v___x_1264_);
                v___x_1266_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___lam__0(v___x_1252_, v___x_1264_, v___x_1265_);
                if v___x_1266_ == 0 {
                    v___y_1257_ = v___y_1263_;
                    state = 2;
                    continue;
                } else {
                    v___x_1267_ = lean_array_fswap(v___y_1263_, v_lo_1239_, v_hi_1240_);
                    v___y_1257_ = v___x_1267_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg___boxed(
    mut v_n_1272_: *mut LeanObject,
    mut v_as_1273_: *mut LeanObject,
    mut v_lo_1274_: *mut LeanObject,
    mut v_hi_1275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1276_: *mut LeanObject = core::ptr::null_mut();
    v_res_1276_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1272_, v_as_1273_, v_lo_1274_, v_hi_1275_);
    lean_dec(v_hi_1275_);
    lean_dec(v_n_1272_);
    return v_res_1276_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(
    mut v_init_1277_: *mut LeanObject,
    mut v_x_1278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1278_) == 0 {
                    v_k_1279_ = lean_ctor_get(v_x_1278_, 1);
                    v_v_1280_ = lean_ctor_get(v_x_1278_, 2);
                    v_l_1281_ = lean_ctor_get(v_x_1278_, 3);
                    v_r_1282_ = lean_ctor_get(v_x_1278_, 4);
                    v___x_1283_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1277_, v_l_1281_);
                    lean_inc(v_v_1280_);
                    lean_inc(v_k_1279_);
                    v___x_1284_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1284_, 0, v_k_1279_);
                    lean_ctor_set(v___x_1284_, 1, v_v_1280_);
                    v___x_1285_ = lean_array_push(v___x_1283_, v___x_1284_);
                    v_init_1277_ = v___x_1285_;
                    v_x_1278_ = v_r_1282_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1277_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0___boxed(
    mut v_init_1287_: *mut LeanObject,
    mut v_x_1288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_res_1289_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1287_, v_x_1288_);
    lean_dec(v_x_1288_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_getErrorExplanationsRaw(mut v_env_1290_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: u8 = 0;
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1291_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_1292_ = lean_ctor_get(v___x_1291_, 0);
                v_asyncMode_1293_ = lean_ctor_get(v_toEnvExtension_1292_, 2);
                v___x_1294_ = lean_box(1);
                v___x_1295_ = lean_box(0);
                v___x_1296_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1294_,
                    v___x_1291_,
                    v_env_1290_,
                    v_asyncMode_1293_,
                    v___x_1295_,
                );
                v___x_1297_ = lean_unsigned_to_nat(0);
                v___x_1298_ = l_Lean_getErrorExplanations___redArg___lam__2___closed__0;
                v___x_1299_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v___x_1298_, v___x_1296_);
                lean_dec(v___x_1296_);
                v___x_1300_ = lean_array_get_size(v___x_1299_);
                v___x_1301_ = lean_nat_dec_eq(v___x_1300_, v___x_1297_);
                if v___x_1301_ == 0 {
                    v___x_1302_ = lean_unsigned_to_nat(1);
                    v___x_1303_ = lean_nat_sub(v___x_1300_, v___x_1302_);
                    v___x_1309_ = lean_nat_dec_le(v___x_1297_, v___x_1303_);
                    if v___x_1309_ == 0 {
                        lean_inc(v___x_1303_);
                        v___y_1305_ = v___x_1303_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1305_ = v___x_1297_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_1299_;
                }
            }
            1 => {
                v___x_1306_ = lean_nat_dec_le(v___y_1305_, v___x_1303_);
                if v___x_1306_ == 0 {
                    lean_dec(v___x_1303_);
                    lean_inc(v___y_1305_);
                    v___x_1307_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_1300_, v___x_1299_, v___y_1305_, v___y_1305_);
                    lean_dec(v___y_1305_);
                    return v___x_1307_;
                } else {
                    v___x_1308_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v___x_1300_, v___x_1299_, v___y_1305_, v___x_1303_);
                    lean_dec(v___x_1303_);
                    return v___x_1308_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(
    mut v_init_1310_: *mut LeanObject,
    mut v_t_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0_spec__0(v_init_1310_, v_t_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0___boxed(
    mut v_init_1313_: *mut LeanObject,
    mut v_t_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1315_: *mut LeanObject = core::ptr::null_mut();
    v_res_1315_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_getErrorExplanationsRaw_spec__0(
        v_init_1313_,
        v_t_1314_,
    );
    lean_dec(v_t_1314_);
    return v_res_1315_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(
    mut v_n_1316_: *mut LeanObject,
    mut v_as_1317_: *mut LeanObject,
    mut v_lo_1318_: *mut LeanObject,
    mut v_hi_1319_: *mut LeanObject,
    mut v_w_1320_: *mut LeanObject,
    mut v_hlo_1321_: *mut LeanObject,
    mut v_hhi_1322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1323_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___redArg(v_n_1316_, v_as_1317_, v_lo_1318_, v_hi_1319_);
    return v___x_1323_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1___boxed(
    mut v_n_1324_: *mut LeanObject,
    mut v_as_1325_: *mut LeanObject,
    mut v_lo_1326_: *mut LeanObject,
    mut v_hi_1327_: *mut LeanObject,
    mut v_w_1328_: *mut LeanObject,
    mut v_hlo_1329_: *mut LeanObject,
    mut v_hhi_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1331_: *mut LeanObject = core::ptr::null_mut();
    v_res_1331_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1(v_n_1324_, v_as_1325_, v_lo_1326_, v_hi_1327_, v_w_1328_, v_hlo_1329_, v_hhi_1330_);
    lean_dec(v_hi_1327_);
    lean_dec(v_n_1324_);
    return v_res_1331_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(
    mut v_n_1332_: *mut LeanObject,
    mut v_lo_1333_: *mut LeanObject,
    mut v_hi_1334_: *mut LeanObject,
    mut v_hhi_1335_: *mut LeanObject,
    mut v_pivot_1336_: *mut LeanObject,
    mut v_as_1337_: *mut LeanObject,
    mut v_i_1338_: *mut LeanObject,
    mut v_k_1339_: *mut LeanObject,
    mut v_ilo_1340_: *mut LeanObject,
    mut v_ik_1341_: *mut LeanObject,
    mut v_w_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___redArg(v_hi_1334_, v_pivot_1336_, v_as_1337_, v_i_1338_, v_k_1339_);
    return v___x_1343_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2___boxed(
    mut v_n_1344_: *mut LeanObject,
    mut v_lo_1345_: *mut LeanObject,
    mut v_hi_1346_: *mut LeanObject,
    mut v_hhi_1347_: *mut LeanObject,
    mut v_pivot_1348_: *mut LeanObject,
    mut v_as_1349_: *mut LeanObject,
    mut v_i_1350_: *mut LeanObject,
    mut v_k_1351_: *mut LeanObject,
    mut v_ilo_1352_: *mut LeanObject,
    mut v_ik_1353_: *mut LeanObject,
    mut v_w_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_res_1355_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_getErrorExplanationsRaw_spec__1_spec__2(v_n_1344_, v_lo_1345_, v_hi_1346_, v_hhi_1347_, v_pivot_1348_, v_as_1349_, v_i_1350_, v_k_1351_, v_ilo_1352_, v_ik_1353_, v_w_1354_);
    lean_dec(v_hi_1346_);
    lean_dec(v_lo_1345_);
    lean_dec(v_n_1344_);
    return v_res_1355_;
}
pub unsafe fn l_Lean_getErrorExplanationsSorted___redArg(
    mut v_inst_1356_: *mut LeanObject,
    mut v_inst_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lean_getErrorExplanations___redArg(v_inst_1356_, v_inst_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_getErrorExplanationsSorted(
    mut v_m_1359_: *mut LeanObject,
    mut v_inst_1360_: *mut LeanObject,
    mut v_inst_1361_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    v___x_1362_ = l_Lean_getErrorExplanations___redArg(v_inst_1360_, v_inst_1361_);
    return v___x_1362_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_DocString_Links(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_ErrorExplanation_0__Lean_initFn_00___x40_Lean_ErrorExplanation_3643637962____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_errorExplanationExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_errorExplanationExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Message(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_EnvExtension(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_DocString_Links(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_ErrorExplanation(builtin);
}
