// Lean compiler output
// Module: Lean.Data.Json.FromToJson.Basic
// Imports: Lean.Data.Json.Printer Init.Data.ToString.Macro Init.Data.Array.GetLit
use crate::r#gen::Init::Control::Except::{
    l_Except_bind, l_Except_instMonad___lam__0, l_Except_instMonad___lam__1,
    l_Except_instMonad___lam__2___boxed, l_Except_instMonad___lam__3, l_Except_map, l_Except_pure,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::GetLit::{
    initialize_Init_Data_Array_GetLit, runtime_initialize_Init_Data_Array_GetLit,
};
use crate::r#gen::Init::Data::OfScientific::l_Float_ofScientific;
use crate::r#gen::Init::Data::Ord::String::l_String_compare___boxed;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::l_String_toSlice;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_decodeNatLitVal_x3f, l_String_toName};
use crate::r#gen::Init::Prelude::{l_Function_comp, l_System_Platform_numBits, l_id___boxed};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getArr_x3f, l_Lean_Json_getBool_x3f___boxed, l_Lean_Json_getInt_x3f,
    l_Lean_Json_getNat_x3f, l_Lean_Json_getNum_x3f, l_Lean_Json_getObjVal_x3f,
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_setObjVal_x21,
    l_Lean_JsonNumber_fromFloat_x3f, l_Lean_JsonNumber_fromInt, l_Lean_JsonNumber_fromNat,
    l_Lean_JsonNumber_toFloat,
};
use crate::r#gen::Lean::Data::Json::Printer::{
    initialize_Lean_Data_Json_Printer, l_Lean_Json_pretty,
    runtime_initialize_Lean_Data_Json_Printer,
};
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getString_x21, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::l_Std_DTreeMap_Internal_Impl_insert_x21___redArg;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::{
    l_Std_DTreeMap_Internal_Impl_foldl___redArg, l_Std_DTreeMap_Internal_Impl_foldlM___redArg,
    l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Float::{lean_float_div, lean_float_negate};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_extract;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_uint64_to_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_pow, lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_box_float, lean_box_uint64, lean_box_usize, lean_closure_set, lean_cstr_to_nat,
    lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_float, lean_unbox_uint64, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_instFromJsonJson___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonJson___closed__0_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_id___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_instToJsonJson___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJson___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonJson: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJson___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonJsonNumber___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_getNum_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonJsonNumber___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJsonNumber___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonJsonNumber: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonJsonNumber___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonJsonNumber___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instToJsonJsonNumber___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToJsonJsonNumber___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJsonNumber___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonJsonNumber: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonJsonNumber___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonUnit___lam__0___closed__0_value: LeanStringObject<33> =
    LeanStringObject {
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 123, 125, 32, 116, 111, 32, 100, 101, 99,
            111, 100, 101, 32, 85, 110, 105, 116, 44, 32, 103, 111, 116, 32, 0,
        ],
    };
static mut l_Lean_instFromJsonUnit___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonUnit___lam__0___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_instFromJsonUnit___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonUnit___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonUnit___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonUnit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonUnit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUnit___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonUnit___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_instToJsonUnit___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonUnit___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonUnit___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonUnit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonUnit: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUnit___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonEmpty___lam__0___closed__0_value: LeanStringObject<52> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            116, 121, 112, 101, 32, 69, 109, 112, 116, 121, 32, 104, 97, 115, 32, 110, 111, 32, 99,
            111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 32, 116, 111, 32, 109, 97, 116, 99,
            104, 32, 74, 83, 79, 78, 32, 118, 97, 108, 117, 101, 32, 39, 0,
        ],
    };
static mut l_Lean_instFromJsonEmpty___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonEmpty___lam__0___closed__1_value: LeanStringObject<122> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 122,
        m_capacity: 122,
        m_length: 121,
        m_data: [
            39, 46, 32, 84, 104, 105, 115, 32, 111, 99, 99, 117, 114, 115, 32, 119, 104, 101, 110,
            32, 100, 101, 115, 101, 114, 105, 97, 108, 105, 122, 105, 110, 103, 32, 97, 32, 118,
            97, 108, 117, 101, 32, 102, 111, 114, 32, 116, 121, 112, 101, 32, 69, 109, 112, 116,
            121, 44, 32, 101, 46, 103, 46, 32, 97, 116, 32, 116, 121, 112, 101, 32, 79, 112, 116,
            105, 111, 110, 32, 69, 109, 112, 116, 121, 32, 119, 105, 116, 104, 32, 99, 111, 100,
            101, 32, 102, 111, 114, 32, 116, 104, 101, 32, 39, 115, 111, 109, 101, 39, 32, 99, 111,
            110, 115, 116, 114, 117, 99, 116, 111, 114, 46, 0,
        ],
    };
static mut l_Lean_instFromJsonEmpty___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonEmpty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonEmpty___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonEmpty: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonEmpty___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonEmpty___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonEmpty___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonEmpty___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonEmpty___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonEmpty: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonEmpty___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_getBool_x3f___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_getNat_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonNat___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_getInt_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonInt___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonInt___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonInt___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_getStr_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonString___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonSlice___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_String_toSlice as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonSlice___closed__1_value: LeanClosureObject<4> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Except_map as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instFromJsonSlice___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonSlice___closed__2_value: LeanClosureObject<5> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 5) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Function_comp as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 5,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instFromJsonString___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instFromJsonSlice___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonSlice: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonSlice___closed__2_value) as *mut LeanObject;
pub static l_Lean_instToJsonSlice___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonSlice___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonSlice___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonSlice___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonSlice: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonSlice___closed__0_value) as *mut LeanObject;
pub static l_Lean_instFromJsonFilePath___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonFilePath___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instFromJsonFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFilePath___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonFilePath___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonFilePath___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonFilePath___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFilePath___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonFilePath: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFilePath___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__1 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Except_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_fromJson_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__4_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_map as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Array_fromJson_x3f___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__6_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_pure as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__7_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__6_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Array_fromJson_x3f___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__8_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Except_bind as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Array_fromJson_x3f___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Array_fromJson_x3f___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__9_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__10_value: LeanStringObject<27> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 74, 83, 79, 78, 32, 97, 114, 114, 97, 121,
            44, 32, 103, 111, 116, 32, 39, 0,
        ],
    };
static mut l_Array_fromJson_x3f___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__10_value) as *mut LeanObject;
pub static l_Array_fromJson_x3f___redArg___closed__11_value: LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Array_fromJson_x3f___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Array_fromJson_x3f___redArg___closed__11_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_toJson___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Array_toJson___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_toJson___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_toJson___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_toJson___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Array_toJson___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_toJson___redArg___closed__9_value) as *mut LeanObject;
pub static l_Option_fromJson_x3f___redArg___closed__0_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Option_fromJson_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_fromJson_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_fromJson_x3f___redArg___closed__0_value: LeanStringObject<21> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 112, 97, 105, 114, 44, 32, 103, 111, 116,
            32, 39, 0,
        ],
    };
static mut l_Prod_fromJson_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Prod_fromJson_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [91, 97, 110, 111, 110, 121, 109, 111, 117, 115, 93, 0],
};
static mut l_Lean_Name_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__1_value: LeanStringObject<25> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 96, 44, 32, 103,
        111, 116, 32, 39, 0,
    ],
};
static mut l_Lean_Name_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Name_fromJson_x3f___closed__2_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Name_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Name_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_instFromJsonName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonName___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonName___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonName___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonName___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value: LeanStringObject<28> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 96, 78, 97, 109, 101, 77, 97, 112,
            96, 44, 32, 103, 111, 116, 32, 39, 0,
        ],
    };
static mut l_Lean_NameMap_fromJson_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_fromJson_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_String_compare___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_NameMap_toJson___redArg___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_NameMap_toJson___redArg___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_bignumFromJson_x3f___closed__0_value: LeanStringObject<40> = LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 115, 116, 114, 105, 110, 103, 45, 101,
        110, 99, 111, 100, 101, 100, 32, 110, 117, 109, 98, 101, 114, 44, 32, 103, 111, 116, 32,
        39, 0,
    ],
};
static mut l_Lean_bignumFromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_bignumFromJson_x3f___closed__0_value) as *mut LeanObject;
static mut l_USize_fromJson_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_USize_fromJson_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_USize_fromJson_x3f___closed__1_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [118, 97, 108, 117, 101, 32, 39, 0],
};
static mut l_USize_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_USize_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_USize_fromJson_x3f___closed__2_value: LeanStringObject<27> = LeanStringObject {
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
        39, 32, 105, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 102, 111, 114, 32, 96,
        85, 83, 105, 122, 101, 96, 0,
    ],
};
static mut l_USize_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_USize_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Lean_instFromJsonUSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_USize_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUSize___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonUSize: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUSize___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonUSize___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonUSize___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonUSize___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUSize___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonUSize: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUSize___closed__0_value) as *mut LeanObject;
static mut l_UInt64_fromJson_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_UInt64_fromJson_x3f___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_UInt64_fromJson_x3f___closed__1_value: LeanStringObject<28> = LeanStringObject {
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
        39, 32, 105, 115, 32, 116, 111, 111, 32, 108, 97, 114, 103, 101, 32, 102, 111, 114, 32, 96,
        85, 73, 110, 116, 54, 52, 96, 0,
    ],
};
static mut l_UInt64_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_UInt64_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_instFromJsonUInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_UInt64_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonUInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUInt64___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonUInt64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonUInt64___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonUInt64___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instToJsonUInt64___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonUInt64___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUInt64___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonUInt64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonUInt64___closed__0_value) as *mut LeanObject;
pub static l_Lean_instToJsonFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_toJson___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instToJsonFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFloat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToJsonFloat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToJsonFloat___closed__0_value) as *mut LeanObject;
pub static l_Float_fromJson_x3f___closed__0_value: LeanStringObject<62> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        69, 120, 112, 101, 99, 116, 101, 100, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111,
        114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 32, 39, 73, 110, 102, 105, 110, 105, 116,
        121, 39, 44, 32, 39, 45, 73, 110, 102, 105, 110, 105, 116, 121, 39, 44, 32, 39, 78, 97, 78,
        39, 46, 0,
    ],
};
static mut l_Float_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Float_fromJson_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Float_fromJson_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Float_fromJson_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__1_value) as *mut LeanObject;
pub static l_Float_fromJson_x3f___closed__2_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [73, 110, 102, 105, 110, 105, 116, 121, 0],
};
static mut l_Float_fromJson_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__2_value) as *mut LeanObject;
pub static l_Float_fromJson_x3f___closed__3_value: LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [45, 73, 110, 102, 105, 110, 105, 116, 121, 0],
};
static mut l_Float_fromJson_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__3_value) as *mut LeanObject;
pub static l_Float_fromJson_x3f___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [78, 97, 78, 0],
};
static mut l_Float_fromJson_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Float_fromJson_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lean_instFromJsonFloat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Float_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instFromJsonFloat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFloat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instFromJsonFloat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instFromJsonFloat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_Structured_fromJson_x3f___closed__0_value: LeanStringObject<34> =
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
            101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 116, 114, 117, 99, 116, 117, 114, 101,
            100, 32, 111, 98, 106, 101, 99, 116, 44, 32, 103, 111, 116, 32, 39, 0,
        ],
    };
static mut l_Lean_Json_Structured_fromJson_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_Structured_fromJson_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instFromJsonStructured___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_Structured_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instFromJsonStructured___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instFromJsonStructured___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instFromJsonStructured: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instFromJsonStructured___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instToJsonStructured___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_Structured_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instToJsonStructured___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToJsonStructured___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instToJsonStructured: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instToJsonStructured___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_parseTagged___closed__0_value: LeanStringObject<29> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102,
        32, 102, 105, 101, 108, 100, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Json_parseTagged___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_parseTagged___closed__1_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 3,
    m_data: [32, 226, 137, 159, 32, 0],
};
static mut l_Lean_Json_parseTagged___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_parseTagged___closed__2_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Json_parseTagged___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__2_value) as *mut LeanObject;
pub static l_Lean_Json_parseTagged___closed__3_value: LeanStringObject<16> = LeanStringObject {
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
        105, 110, 99, 111, 114, 114, 101, 99, 116, 32, 116, 97, 103, 58, 32, 0,
    ],
};
static mut l_Lean_Json_parseTagged___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__3_value) as *mut LeanObject;
pub static l_Lean_Json_parseTagged___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__2_value) as *mut LeanObject],
};
static mut l_Lean_Json_parseTagged___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_parseTagged___closed__4_value) as *mut LeanObject;
pub unsafe fn l_Lean_instFromJsonJson___lam__0(mut v_a_1054_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1055_, 0, v_a_1054_);
    return v___x_1055_;
}
pub unsafe fn l_Lean_instToJsonJsonNumber___lam__0(
    mut v_n_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    v___x_1063_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1063_, 0, v_n_1062_);
    return v___x_1063_;
}
pub unsafe fn l_Lean_instFromJsonUnit___lam__0(mut v_x_1069_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1069_) == 5 {
                    v_kvPairs_1076_ = lean_ctor_get(v_x_1069_, 0);
                    if lean_obj_tag(v_kvPairs_1076_) == 1 {
                        lean_dec_ref_known(v_x_1069_, 1);
                        v___x_1077_ = l_Lean_instFromJsonUnit___lam__0___closed__1;
                        return v___x_1077_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1071_ = l_Lean_instFromJsonUnit___lam__0___closed__0;
                v___x_1072_ = lean_unsigned_to_nat(80);
                v___x_1073_ = l_Lean_Json_pretty(v_x_1069_, v___x_1072_);
                v___x_1074_ = lean_string_append(v___x_1071_, v___x_1073_);
                lean_dec_ref(v___x_1073_);
                v___x_1075_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1075_, 0, v___x_1074_);
                return v___x_1075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUnit___lam__0(mut v_x_1082_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    v___x_1083_ = l_Lean_instToJsonUnit___lam__0___closed__0;
    return v___x_1083_;
}
pub unsafe fn l_Lean_instFromJsonEmpty___lam__0(mut v_j_1088_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    v___x_1089_ = l_Lean_instFromJsonEmpty___lam__0___closed__0;
    v___x_1090_ = lean_unsigned_to_nat(80);
    v___x_1091_ = l_Lean_Json_pretty(v_j_1088_, v___x_1090_);
    v___x_1092_ = lean_string_append(v___x_1089_, v___x_1091_);
    lean_dec_ref(v___x_1091_);
    v___x_1093_ = l_Lean_instFromJsonEmpty___lam__0___closed__1;
    v___x_1094_ = lean_string_append(v___x_1092_, v___x_1093_);
    v___x_1095_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1095_, 0, v___x_1094_);
    return v___x_1095_;
}
pub unsafe fn l_Lean_instToJsonEmpty___lam__0(mut v_a_1098_: u8) -> *mut LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_Lean_instToJsonEmpty___lam__0___boxed(
    mut v_a_1099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6__boxed_1100_: u8 = 0;
    let mut v_res_1101_: *mut LeanObject = core::ptr::null_mut();
    v_a_6__boxed_1100_ = (lean_unbox(v_a_1099_) as u8);
    v_res_1101_ = l_Lean_instToJsonEmpty___lam__0(v_a_6__boxed_1100_);
    return v_res_1101_;
}
pub unsafe fn l_Lean_instToJsonBool___lam__0(mut v_b_1106_: u8) -> *mut LeanObject {
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v___x_1107_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_1107_, 0 as u32, v_b_1106_);
    return v___x_1107_;
}
pub unsafe fn l_Lean_instToJsonBool___lam__0___boxed(
    mut v_b_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_1109_: u8 = 0;
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1109_ = (lean_unbox(v_b_1108_) as u8);
    v_res_1110_ = l_Lean_instToJsonBool___lam__0(v_b_boxed_1109_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_instToJsonNat___lam__0(mut v_n_1115_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    v___x_1116_ = l_Lean_JsonNumber_fromNat(v_n_1115_);
    v___x_1117_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1117_, 0, v___x_1116_);
    return v___x_1117_;
}
pub unsafe fn l_Lean_instToJsonInt___lam__0(mut v_n_1122_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_JsonNumber_fromInt(v_n_1122_);
    v___x_1124_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1124_, 0, v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn l_Lean_instToJsonString___lam__0(mut v_s_1129_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    v___x_1130_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1130_, 0, v_s_1129_);
    return v___x_1130_;
}
pub unsafe fn l_Lean_instToJsonSlice___lam__0(mut v_s_1140_: *mut LeanObject) -> *mut LeanObject {
    let mut v_str_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v_str_1141_ = lean_ctor_get(v_s_1140_, 0);
    v_startInclusive_1142_ = lean_ctor_get(v_s_1140_, 1);
    v_endExclusive_1143_ = lean_ctor_get(v_s_1140_, 2);
    v___x_1144_ =
        lean_string_utf8_extract(v_str_1141_, v_startInclusive_1142_, v_endExclusive_1143_);
    v___x_1145_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1145_, 0, v___x_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_instToJsonSlice___lam__0___boxed(
    mut v_s_1146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1147_: *mut LeanObject = core::ptr::null_mut();
    v_res_1147_ = l_Lean_instToJsonSlice___lam__0(v_s_1146_);
    lean_dec_ref(v_s_1146_);
    return v_res_1147_;
}
pub unsafe fn l_Lean_instFromJsonFilePath___lam__0(
    mut v_j_1150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1159_: u8 = 0;
    let mut v_a_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1163_: u8 = 0;
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1167_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1151_ = l_Lean_Json_getStr_x3f(v_j_1150_);
                if lean_obj_tag(v___x_1151_) == 0 {
                    v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
                    v_isSharedCheck_1159_ = (!lean_is_exclusive(v___x_1151_)) as u8;
                    if v_isSharedCheck_1159_ == 0 {
                        v___x_1154_ = v___x_1151_;
                        v_isShared_1155_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1152_);
                        lean_dec(v___x_1151_);
                        v___x_1154_ = lean_box(0);
                        v_isShared_1155_ = v_isSharedCheck_1159_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1160_ = lean_ctor_get(v___x_1151_, 0);
                    v_isSharedCheck_1167_ = (!lean_is_exclusive(v___x_1151_)) as u8;
                    if v_isSharedCheck_1167_ == 0 {
                        v___x_1162_ = v___x_1151_;
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1160_);
                        lean_dec(v___x_1151_);
                        v___x_1162_ = lean_box(0);
                        v_isShared_1163_ = v_isSharedCheck_1167_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1155_ == 0 {
                    v___x_1157_ = v___x_1154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
                    v___x_1157_ = v_reuseFailAlloc_1158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1157_;
            }
            3 => {
                if v_isShared_1163_ == 0 {
                    v___x_1165_ = v___x_1162_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
                    v___x_1165_ = v_reuseFailAlloc_1166_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1165_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonFilePath___lam__0(
    mut v_p_1170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    v___x_1171_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1171_, 0, v_p_1170_);
    return v___x_1171_;
}
pub unsafe fn l_Array_fromJson_x3f___redArg(
    mut v_inst_1195_: *mut LeanObject,
    mut v_x_1196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Array_fromJson_x3f___redArg___closed__9;
    if lean_obj_tag(v_x_1196_) == 4 {
        let mut v_elems_1198_: *mut LeanObject = core::ptr::null_mut();
        let mut v_sz_1199_: usize = 0;
        let mut v___x_1200_: usize = 0;
        let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
        v_elems_1198_ = lean_ctor_get(v_x_1196_, 0);
        lean_inc_ref(v_elems_1198_);
        lean_dec_ref_known(v_x_1196_, 1);
        v_sz_1199_ = lean_array_size(v_elems_1198_);
        v___x_1200_ = 0usize;
        v___x_1201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
            lean_box(0),
            lean_box(0),
            lean_box(0),
            v___x_1197_,
            v_inst_1195_,
            v_sz_1199_,
            v___x_1200_,
            v_elems_1198_,
        );
        return v___x_1201_;
    } else {
        let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1195_);
        v___x_1202_ = l_Array_fromJson_x3f___redArg___closed__10;
        v___x_1203_ = lean_unsigned_to_nat(80);
        v___x_1204_ = l_Lean_Json_pretty(v_x_1196_, v___x_1203_);
        v___x_1205_ = lean_string_append(v___x_1202_, v___x_1204_);
        lean_dec_ref(v___x_1204_);
        v___x_1206_ = l_Array_fromJson_x3f___redArg___closed__11;
        v___x_1207_ = lean_string_append(v___x_1205_, v___x_1206_);
        v___x_1208_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1208_, 0, v___x_1207_);
        return v___x_1208_;
    }
}
pub unsafe fn l_Array_fromJson_x3f(
    mut v_00_u03b1_1209_: *mut LeanObject,
    mut v_inst_1210_: *mut LeanObject,
    mut v_x_1211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1212_: *mut LeanObject = core::ptr::null_mut();
    v___x_1212_ = l_Array_fromJson_x3f___redArg(v_inst_1210_, v_x_1211_);
    return v___x_1212_;
}
pub unsafe fn l_Lean_instFromJsonArray___redArg(
    mut v_inst_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    v___x_1214_ = lean_alloc_closure(l_Array_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1214_, 0, lean_box(0));
    lean_closure_set(v___x_1214_, 1, v_inst_1213_);
    return v___x_1214_;
}
pub unsafe fn l_Lean_instFromJsonArray(
    mut v_00_u03b1_1215_: *mut LeanObject,
    mut v_inst_1216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ = lean_alloc_closure(l_Array_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1217_, 0, lean_box(0));
    lean_closure_set(v___x_1217_, 1, v_inst_1216_);
    return v___x_1217_;
}
pub unsafe fn l_Array_toJson___redArg___lam__0(
    mut v_inst_1218_: *mut LeanObject,
    mut v_x_1219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_apply_1(v_inst_1218_, v_x_1219_);
    return v___x_1220_;
}
pub unsafe fn l_Array_toJson___redArg(
    mut v_inst_1240_: *mut LeanObject,
    mut v_a_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1244_: usize = 0;
    let mut v___x_1245_: usize = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    v___f_1242_ = lean_alloc_closure(
        l_Array_toJson___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1242_, 0, v_inst_1240_);
    v___x_1243_ = l_Array_toJson___redArg___closed__9;
    v_sz_1244_ = lean_array_size(v_a_1241_);
    v___x_1245_ = 0usize;
    v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        lean_box(0),
        lean_box(0),
        lean_box(0),
        v___x_1243_,
        v___f_1242_,
        v_sz_1244_,
        v___x_1245_,
        v_a_1241_,
    );
    v___x_1247_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1247_, 0, v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn l_Array_toJson(
    mut v_00_u03b1_1248_: *mut LeanObject,
    mut v_inst_1249_: *mut LeanObject,
    mut v_a_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_Array_toJson___redArg(v_inst_1249_, v_a_1250_);
    return v___x_1251_;
}
pub unsafe fn l_Lean_instToJsonArray___redArg(
    mut v_inst_1252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    v___x_1253_ = lean_alloc_closure(l_Array_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1253_, 0, lean_box(0));
    lean_closure_set(v___x_1253_, 1, v_inst_1252_);
    return v___x_1253_;
}
pub unsafe fn l_Lean_instToJsonArray(
    mut v_00_u03b1_1254_: *mut LeanObject,
    mut v_inst_1255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    v___x_1256_ = lean_alloc_closure(l_Array_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1256_, 0, lean_box(0));
    lean_closure_set(v___x_1256_, 1, v_inst_1255_);
    return v___x_1256_;
}
pub unsafe fn l_List_fromJson_x3f___redArg(
    mut v_inst_1257_: *mut LeanObject,
    mut v_j_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1263_: u8 = 0;
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1267_: u8 = 0;
    let mut v_a_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1271_: u8 = 0;
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1259_ = l_Array_fromJson_x3f___redArg(v_inst_1257_, v_j_1258_);
                if lean_obj_tag(v___x_1259_) == 0 {
                    v_a_1260_ = lean_ctor_get(v___x_1259_, 0);
                    v_isSharedCheck_1267_ = (!lean_is_exclusive(v___x_1259_)) as u8;
                    if v_isSharedCheck_1267_ == 0 {
                        v___x_1262_ = v___x_1259_;
                        v_isShared_1263_ = v_isSharedCheck_1267_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1260_);
                        lean_dec(v___x_1259_);
                        v___x_1262_ = lean_box(0);
                        v_isShared_1263_ = v_isSharedCheck_1267_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1268_ = lean_ctor_get(v___x_1259_, 0);
                    v_isSharedCheck_1276_ = (!lean_is_exclusive(v___x_1259_)) as u8;
                    if v_isSharedCheck_1276_ == 0 {
                        v___x_1270_ = v___x_1259_;
                        v_isShared_1271_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1268_);
                        lean_dec(v___x_1259_);
                        v___x_1270_ = lean_box(0);
                        v_isShared_1271_ = v_isSharedCheck_1276_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1263_ == 0 {
                    v___x_1265_ = v___x_1262_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
                    v___x_1265_ = v_reuseFailAlloc_1266_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1265_;
            }
            3 => {
                v___x_1272_ = lean_array_to_list(v_a_1268_);
                if v_isShared_1271_ == 0 {
                    lean_ctor_set(v___x_1270_, 0, v___x_1272_);
                    v___x_1274_ = v___x_1270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
                    v___x_1274_ = v_reuseFailAlloc_1275_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1274_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_fromJson_x3f(
    mut v_00_u03b1_1277_: *mut LeanObject,
    mut v_inst_1278_: *mut LeanObject,
    mut v_j_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    v___x_1280_ = l_List_fromJson_x3f___redArg(v_inst_1278_, v_j_1279_);
    return v___x_1280_;
}
pub unsafe fn l_Lean_instFromJsonList___redArg(
    mut v_inst_1281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    v___x_1282_ = lean_alloc_closure(l_List_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1282_, 0, lean_box(0));
    lean_closure_set(v___x_1282_, 1, v_inst_1281_);
    return v___x_1282_;
}
pub unsafe fn l_Lean_instFromJsonList(
    mut v_00_u03b1_1283_: *mut LeanObject,
    mut v_inst_1284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    v___x_1285_ = lean_alloc_closure(l_List_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1285_, 0, lean_box(0));
    lean_closure_set(v___x_1285_, 1, v_inst_1284_);
    return v___x_1285_;
}
pub unsafe fn l_List_toJson___redArg(
    mut v_inst_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
    v___x_1288_ = lean_array_mk(v_a_1287_);
    v___x_1289_ = l_Array_toJson___redArg(v_inst_1286_, v___x_1288_);
    return v___x_1289_;
}
pub unsafe fn l_List_toJson(
    mut v_00_u03b1_1290_: *mut LeanObject,
    mut v_inst_1291_: *mut LeanObject,
    mut v_a_1292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    v___x_1293_ = l_List_toJson___redArg(v_inst_1291_, v_a_1292_);
    return v___x_1293_;
}
pub unsafe fn l_Lean_instToJsonList___redArg(mut v_inst_1294_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    v___x_1295_ = lean_alloc_closure(l_List_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1295_, 0, lean_box(0));
    lean_closure_set(v___x_1295_, 1, v_inst_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lean_instToJsonList(
    mut v_00_u03b1_1296_: *mut LeanObject,
    mut v_inst_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    v___x_1298_ = lean_alloc_closure(l_List_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1298_, 0, lean_box(0));
    lean_closure_set(v___x_1298_, 1, v_inst_1297_);
    return v___x_1298_;
}
pub unsafe fn l_Option_fromJson_x3f___redArg(
    mut v_inst_1301_: *mut LeanObject,
    mut v_x_1302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1308_: u8 = 0;
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1312_: u8 = 0;
    let mut v_a_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1302_) == 0 {
                    lean_dec_ref(v_inst_1301_);
                    v___x_1303_ = l_Option_fromJson_x3f___redArg___closed__0;
                    return v___x_1303_;
                } else {
                    v___x_1304_ = lean_apply_1(v_inst_1301_, v_x_1302_);
                    if lean_obj_tag(v___x_1304_) == 0 {
                        v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
                        v_isSharedCheck_1312_ = (!lean_is_exclusive(v___x_1304_)) as u8;
                        if v_isSharedCheck_1312_ == 0 {
                            v___x_1307_ = v___x_1304_;
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1305_);
                            lean_dec(v___x_1304_);
                            v___x_1307_ = lean_box(0);
                            v_isShared_1308_ = v_isSharedCheck_1312_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1313_ = lean_ctor_get(v___x_1304_, 0);
                        v_isSharedCheck_1321_ = (!lean_is_exclusive(v___x_1304_)) as u8;
                        if v_isSharedCheck_1321_ == 0 {
                            v___x_1315_ = v___x_1304_;
                            v_isShared_1316_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1313_);
                            lean_dec(v___x_1304_);
                            v___x_1315_ = lean_box(0);
                            v_isShared_1316_ = v_isSharedCheck_1321_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1308_ == 0 {
                    v___x_1310_ = v___x_1307_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1311_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1311_, 0, v_a_1305_);
                    v___x_1310_ = v_reuseFailAlloc_1311_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1310_;
            }
            3 => {
                v___x_1317_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v_a_1313_);
                if v_isShared_1316_ == 0 {
                    lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                    v___x_1319_ = v_reuseFailAlloc_1320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_fromJson_x3f(
    mut v_00_u03b1_1322_: *mut LeanObject,
    mut v_inst_1323_: *mut LeanObject,
    mut v_x_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Option_fromJson_x3f___redArg(v_inst_1323_, v_x_1324_);
    return v___x_1325_;
}
pub unsafe fn l_Lean_instFromJsonOption___redArg(
    mut v_inst_1326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    v___x_1327_ = lean_alloc_closure(l_Option_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1327_, 0, lean_box(0));
    lean_closure_set(v___x_1327_, 1, v_inst_1326_);
    return v___x_1327_;
}
pub unsafe fn l_Lean_instFromJsonOption(
    mut v_00_u03b1_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    v___x_1330_ = lean_alloc_closure(l_Option_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1330_, 0, lean_box(0));
    lean_closure_set(v___x_1330_, 1, v_inst_1329_);
    return v___x_1330_;
}
pub unsafe fn l_Option_toJson___redArg(
    mut v_inst_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1332_) == 0 {
        let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1331_);
        v___x_1333_ = lean_box(0);
        return v___x_1333_;
    } else {
        let mut v_val_1334_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
        v_val_1334_ = lean_ctor_get(v_x_1332_, 0);
        lean_inc(v_val_1334_);
        lean_dec_ref_known(v_x_1332_, 1);
        v___x_1335_ = lean_apply_1(v_inst_1331_, v_val_1334_);
        return v___x_1335_;
    }
}
pub unsafe fn l_Option_toJson(
    mut v_00_u03b1_1336_: *mut LeanObject,
    mut v_inst_1337_: *mut LeanObject,
    mut v_x_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = l_Option_toJson___redArg(v_inst_1337_, v_x_1338_);
    return v___x_1339_;
}
pub unsafe fn l_Lean_instToJsonOption___redArg(
    mut v_inst_1340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    v___x_1341_ = lean_alloc_closure(l_Option_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1341_, 0, lean_box(0));
    lean_closure_set(v___x_1341_, 1, v_inst_1340_);
    return v___x_1341_;
}
pub unsafe fn l_Lean_instToJsonOption(
    mut v_00_u03b1_1342_: *mut LeanObject,
    mut v_inst_1343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
    v___x_1344_ = lean_alloc_closure(l_Option_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1344_, 0, lean_box(0));
    lean_closure_set(v___x_1344_, 1, v_inst_1343_);
    return v___x_1344_;
}
pub unsafe fn l_Prod_fromJson_x3f___redArg(
    mut v_inst_1346_: *mut LeanObject,
    mut v_inst_1347_: *mut LeanObject,
    mut v_x_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_j_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1368_: u8 = 0;
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_a_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1380_: u8 = 0;
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1384_: u8 = 0;
    let mut v_a_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1388_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1393_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1348_) == 4 {
                    v_elems_1358_ = lean_ctor_get(v_x_1348_, 0);
                    v___x_1359_ = lean_array_get_size(v_elems_1358_);
                    v___x_1360_ = lean_unsigned_to_nat(2);
                    v___x_1361_ = lean_nat_dec_eq(v___x_1359_, v___x_1360_);
                    if v___x_1361_ == 0 {
                        lean_dec_ref(v_inst_1347_);
                        lean_dec_ref(v_inst_1346_);
                        v_j_1350_ = v_x_1348_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc_ref(v_elems_1358_);
                        lean_dec_ref_known(v_x_1348_, 1);
                        v___x_1362_ = lean_unsigned_to_nat(0);
                        v___x_1363_ = lean_array_fget_borrowed(v_elems_1358_, v___x_1362_);
                        lean_inc(v___x_1363_);
                        v___x_1364_ = lean_apply_1(v_inst_1346_, v___x_1363_);
                        if lean_obj_tag(v___x_1364_) == 0 {
                            lean_dec_ref(v_elems_1358_);
                            lean_dec_ref(v_inst_1347_);
                            v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
                            v_isSharedCheck_1372_ = (!lean_is_exclusive(v___x_1364_)) as u8;
                            if v_isSharedCheck_1372_ == 0 {
                                v___x_1367_ = v___x_1364_;
                                v_isShared_1368_ = v_isSharedCheck_1372_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1365_);
                                lean_dec(v___x_1364_);
                                v___x_1367_ = lean_box(0);
                                v_isShared_1368_ = v_isSharedCheck_1372_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1373_ = lean_ctor_get(v___x_1364_, 0);
                            lean_inc(v_a_1373_);
                            lean_dec_ref_known(v___x_1364_, 1);
                            v___x_1374_ = lean_unsigned_to_nat(1);
                            v___x_1375_ = lean_array_fget(v_elems_1358_, v___x_1374_);
                            lean_dec_ref(v_elems_1358_);
                            v___x_1376_ = lean_apply_1(v_inst_1347_, v___x_1375_);
                            if lean_obj_tag(v___x_1376_) == 0 {
                                lean_dec(v_a_1373_);
                                v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
                                v_isSharedCheck_1384_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                                if v_isSharedCheck_1384_ == 0 {
                                    v___x_1379_ = v___x_1376_;
                                    v_isShared_1380_ = v_isSharedCheck_1384_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_1377_);
                                    lean_dec(v___x_1376_);
                                    v___x_1379_ = lean_box(0);
                                    v_isShared_1380_ = v_isSharedCheck_1384_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v_a_1385_ = lean_ctor_get(v___x_1376_, 0);
                                v_isSharedCheck_1393_ = (!lean_is_exclusive(v___x_1376_)) as u8;
                                if v_isSharedCheck_1393_ == 0 {
                                    v___x_1387_ = v___x_1376_;
                                    v_isShared_1388_ = v_isSharedCheck_1393_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1385_);
                                    lean_dec(v___x_1376_);
                                    v___x_1387_ = lean_box(0);
                                    v_isShared_1388_ = v_isSharedCheck_1393_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_inst_1347_);
                    lean_dec_ref(v_inst_1346_);
                    v_j_1350_ = v_x_1348_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1351_ = l_Prod_fromJson_x3f___redArg___closed__0;
                v___x_1352_ = lean_unsigned_to_nat(80);
                v___x_1353_ = l_Lean_Json_pretty(v_j_1350_, v___x_1352_);
                v___x_1354_ = lean_string_append(v___x_1351_, v___x_1353_);
                lean_dec_ref(v___x_1353_);
                v___x_1355_ = l_Array_fromJson_x3f___redArg___closed__11;
                v___x_1356_ = lean_string_append(v___x_1354_, v___x_1355_);
                v___x_1357_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1357_, 0, v___x_1356_);
                return v___x_1357_;
            }
            2 => {
                if v_isShared_1368_ == 0 {
                    v___x_1370_ = v___x_1367_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
                    v___x_1370_ = v_reuseFailAlloc_1371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1370_;
            }
            4 => {
                if v_isShared_1380_ == 0 {
                    v___x_1382_ = v___x_1379_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
                    v___x_1382_ = v_reuseFailAlloc_1383_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1382_;
            }
            6 => {
                v___x_1389_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1389_, 0, v_a_1373_);
                lean_ctor_set(v___x_1389_, 1, v_a_1385_);
                if v_isShared_1388_ == 0 {
                    lean_ctor_set(v___x_1387_, 0, v___x_1389_);
                    v___x_1391_ = v___x_1387_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1392_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1392_, 0, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1392_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1391_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_fromJson_x3f(
    mut v_00_u03b1_1394_: *mut LeanObject,
    mut v_00_u03b2_1395_: *mut LeanObject,
    mut v_inst_1396_: *mut LeanObject,
    mut v_inst_1397_: *mut LeanObject,
    mut v_x_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Prod_fromJson_x3f___redArg(v_inst_1396_, v_inst_1397_, v_x_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_instFromJsonProd___redArg(
    mut v_inst_1400_: *mut LeanObject,
    mut v_inst_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1402_ = lean_alloc_closure(l_Prod_fromJson_x3f as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1402_, 0, lean_box(0));
    lean_closure_set(v___x_1402_, 1, lean_box(0));
    lean_closure_set(v___x_1402_, 2, v_inst_1400_);
    lean_closure_set(v___x_1402_, 3, v_inst_1401_);
    return v___x_1402_;
}
pub unsafe fn l_Lean_instFromJsonProd(
    mut v_00_u03b1_1403_: *mut LeanObject,
    mut v_00_u03b2_1404_: *mut LeanObject,
    mut v_inst_1405_: *mut LeanObject,
    mut v_inst_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ = lean_alloc_closure(l_Prod_fromJson_x3f as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1407_, 0, lean_box(0));
    lean_closure_set(v___x_1407_, 1, lean_box(0));
    lean_closure_set(v___x_1407_, 2, v_inst_1405_);
    lean_closure_set(v___x_1407_, 3, v_inst_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Prod_toJson___redArg(
    mut v_inst_1408_: *mut LeanObject,
    mut v_inst_1409_: *mut LeanObject,
    mut v_x_1410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1411_ = lean_ctor_get(v_x_1410_, 0);
    lean_inc(v_fst_1411_);
    v_snd_1412_ = lean_ctor_get(v_x_1410_, 1);
    lean_inc(v_snd_1412_);
    lean_dec_ref(v_x_1410_);
    v___x_1413_ = lean_apply_1(v_inst_1408_, v_fst_1411_);
    v___x_1414_ = lean_apply_1(v_inst_1409_, v_snd_1412_);
    v___x_1415_ = lean_unsigned_to_nat(2);
    v___x_1416_ = lean_mk_empty_array_with_capacity(v___x_1415_);
    v___x_1417_ = lean_array_push(v___x_1416_, v___x_1413_);
    v___x_1418_ = lean_array_push(v___x_1417_, v___x_1414_);
    v___x_1419_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1419_, 0, v___x_1418_);
    return v___x_1419_;
}
pub unsafe fn l_Prod_toJson(
    mut v_00_u03b1_1420_: *mut LeanObject,
    mut v_00_u03b2_1421_: *mut LeanObject,
    mut v_inst_1422_: *mut LeanObject,
    mut v_inst_1423_: *mut LeanObject,
    mut v_x_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1425_ = l_Prod_toJson___redArg(v_inst_1422_, v_inst_1423_, v_x_1424_);
    return v___x_1425_;
}
pub unsafe fn l_Lean_instToJsonProd___redArg(
    mut v_inst_1426_: *mut LeanObject,
    mut v_inst_1427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1428_ = lean_alloc_closure(l_Prod_toJson as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1428_, 0, lean_box(0));
    lean_closure_set(v___x_1428_, 1, lean_box(0));
    lean_closure_set(v___x_1428_, 2, v_inst_1426_);
    lean_closure_set(v___x_1428_, 3, v_inst_1427_);
    return v___x_1428_;
}
pub unsafe fn l_Lean_instToJsonProd(
    mut v_00_u03b1_1429_: *mut LeanObject,
    mut v_00_u03b2_1430_: *mut LeanObject,
    mut v_inst_1431_: *mut LeanObject,
    mut v_inst_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_alloc_closure(l_Prod_toJson as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_1433_, 0, lean_box(0));
    lean_closure_set(v___x_1433_, 1, lean_box(0));
    lean_closure_set(v___x_1433_, 2, v_inst_1431_);
    lean_closure_set(v___x_1433_, 3, v_inst_1432_);
    return v___x_1433_;
}
pub unsafe fn l_Lean_Name_fromJson_x3f(mut v_j_1438_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1443_: u8 = 0;
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1447_: u8 = 0;
    let mut v_a_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1451_: u8 = 0;
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: u8 = 0;
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: u8 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1469_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_1438_);
                v___x_1439_ = l_Lean_Json_getStr_x3f(v_j_1438_);
                if lean_obj_tag(v___x_1439_) == 0 {
                    lean_dec(v_j_1438_);
                    v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1447_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1447_ == 0 {
                        v___x_1442_ = v___x_1439_;
                        v_isShared_1443_ = v_isSharedCheck_1447_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1440_);
                        lean_dec(v___x_1439_);
                        v___x_1442_ = lean_box(0);
                        v_isShared_1443_ = v_isSharedCheck_1447_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1448_ = lean_ctor_get(v___x_1439_, 0);
                    v_isSharedCheck_1469_ = (!lean_is_exclusive(v___x_1439_)) as u8;
                    if v_isSharedCheck_1469_ == 0 {
                        v___x_1450_ = v___x_1439_;
                        v_isShared_1451_ = v_isSharedCheck_1469_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1448_);
                        lean_dec(v___x_1439_);
                        v___x_1450_ = lean_box(0);
                        v_isShared_1451_ = v_isSharedCheck_1469_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1443_ == 0 {
                    v___x_1445_ = v___x_1442_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
                    v___x_1445_ = v_reuseFailAlloc_1446_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1445_;
            }
            3 => {
                v___x_1452_ = l_Lean_Name_fromJson_x3f___closed__0;
                v___x_1453_ = lean_string_dec_eq(v_a_1448_, v___x_1452_);
                if v___x_1453_ == 0 {
                    v___x_1454_ = l_String_toName(v_a_1448_);
                    v___x_1455_ = l_Lean_Name_isAnonymous(v___x_1454_);
                    if v___x_1455_ == 0 {
                        lean_dec(v_j_1438_);
                        if v_isShared_1451_ == 0 {
                            lean_ctor_set(v___x_1450_, 0, v___x_1454_);
                            v___x_1457_ = v___x_1450_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1458_, 0, v___x_1454_);
                            v___x_1457_ = v_reuseFailAlloc_1458_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1454_);
                        v___x_1459_ = l_Lean_Name_fromJson_x3f___closed__1;
                        v___x_1460_ = lean_unsigned_to_nat(80);
                        v___x_1461_ = l_Lean_Json_pretty(v_j_1438_, v___x_1460_);
                        v___x_1462_ = lean_string_append(v___x_1459_, v___x_1461_);
                        lean_dec_ref(v___x_1461_);
                        v___x_1463_ = l_Array_fromJson_x3f___redArg___closed__11;
                        v___x_1464_ = lean_string_append(v___x_1462_, v___x_1463_);
                        if v_isShared_1451_ == 0 {
                            lean_ctor_set_tag(v___x_1450_, 0);
                            lean_ctor_set(v___x_1450_, 0, v___x_1464_);
                            v___x_1466_ = v___x_1450_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1464_);
                            v___x_1466_ = v_reuseFailAlloc_1467_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1450_);
                    lean_dec(v_a_1448_);
                    lean_dec(v_j_1438_);
                    v___x_1468_ = l_Lean_Name_fromJson_x3f___closed__2;
                    return v___x_1468_;
                }
            }
            4 => {
                return v___x_1457_;
            }
            5 => {
                return v___x_1466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonName___lam__0(mut v_n_1472_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1473_: u8 = 0;
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_1473_ = 1;
    v___x_1474_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1472_, v___x_1473_);
    v___x_1475_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1475_, 0, v___x_1474_);
    return v___x_1475_;
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___redArg___lam__0(
    mut v_inst_1478_: *mut LeanObject,
    mut v_m_1479_: *mut LeanObject,
    mut v_k_1480_: *mut LeanObject,
    mut v_v_1481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: u8 = 0;
    let mut v_n_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1490_: u8 = 0;
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut v_a_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1498_: u8 = 0;
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1517_: u8 = 0;
    let mut v_a_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1521_: u8 = 0;
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1482_ = l_Lean_Name_fromJson_x3f___closed__0;
                v___x_1483_ = lean_string_dec_eq(v_k_1480_, v___x_1482_);
                if v___x_1483_ == 0 {
                    lean_inc_ref(v_k_1480_);
                    v_n_1484_ = l_String_toName(v_k_1480_);
                    v___x_1485_ = l_Lean_Name_isAnonymous(v_n_1484_);
                    if v___x_1485_ == 0 {
                        lean_dec_ref(v_k_1480_);
                        v___x_1486_ = lean_apply_1(v_inst_1478_, v_v_1481_);
                        if lean_obj_tag(v___x_1486_) == 0 {
                            lean_dec(v_n_1484_);
                            lean_dec(v_m_1479_);
                            v_a_1487_ = lean_ctor_get(v___x_1486_, 0);
                            v_isSharedCheck_1494_ = (!lean_is_exclusive(v___x_1486_)) as u8;
                            if v_isSharedCheck_1494_ == 0 {
                                v___x_1489_ = v___x_1486_;
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1487_);
                                lean_dec(v___x_1486_);
                                v___x_1489_ = lean_box(0);
                                v_isShared_1490_ = v_isSharedCheck_1494_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1495_ = lean_ctor_get(v___x_1486_, 0);
                            v_isSharedCheck_1503_ = (!lean_is_exclusive(v___x_1486_)) as u8;
                            if v_isSharedCheck_1503_ == 0 {
                                v___x_1497_ = v___x_1486_;
                                v_isShared_1498_ = v_isSharedCheck_1503_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1495_);
                                lean_dec(v___x_1486_);
                                v___x_1497_ = lean_box(0);
                                v_isShared_1498_ = v_isSharedCheck_1503_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_n_1484_);
                        lean_dec(v_v_1481_);
                        lean_dec(v_m_1479_);
                        lean_dec_ref(v_inst_1478_);
                        v___x_1504_ = l_Lean_Name_fromJson_x3f___closed__1;
                        v___x_1505_ = lean_string_append(v___x_1504_, v_k_1480_);
                        lean_dec_ref(v_k_1480_);
                        v___x_1506_ = l_Array_fromJson_x3f___redArg___closed__11;
                        v___x_1507_ = lean_string_append(v___x_1505_, v___x_1506_);
                        v___x_1508_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1508_, 0, v___x_1507_);
                        return v___x_1508_;
                    }
                } else {
                    lean_dec_ref(v_k_1480_);
                    v___x_1509_ = lean_apply_1(v_inst_1478_, v_v_1481_);
                    if lean_obj_tag(v___x_1509_) == 0 {
                        lean_dec(v_m_1479_);
                        v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
                        v_isSharedCheck_1517_ = (!lean_is_exclusive(v___x_1509_)) as u8;
                        if v_isSharedCheck_1517_ == 0 {
                            v___x_1512_ = v___x_1509_;
                            v_isShared_1513_ = v_isSharedCheck_1517_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_1510_);
                            lean_dec(v___x_1509_);
                            v___x_1512_ = lean_box(0);
                            v_isShared_1513_ = v_isSharedCheck_1517_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_1518_ = lean_ctor_get(v___x_1509_, 0);
                        v_isSharedCheck_1527_ = (!lean_is_exclusive(v___x_1509_)) as u8;
                        if v_isSharedCheck_1527_ == 0 {
                            v___x_1520_ = v___x_1509_;
                            v_isShared_1521_ = v_isSharedCheck_1527_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1518_);
                            lean_dec(v___x_1509_);
                            v___x_1520_ = lean_box(0);
                            v_isShared_1521_ = v_isSharedCheck_1527_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1490_ == 0 {
                    v___x_1492_ = v___x_1489_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_a_1487_);
                    v___x_1492_ = v_reuseFailAlloc_1493_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1492_;
            }
            3 => {
                v___x_1499_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_n_1484_, v_a_1495_, v_m_1479_);
                if v_isShared_1498_ == 0 {
                    lean_ctor_set(v___x_1497_, 0, v___x_1499_);
                    v___x_1501_ = v___x_1497_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1502_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1499_);
                    v___x_1501_ = v_reuseFailAlloc_1502_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1501_;
            }
            5 => {
                if v_isShared_1513_ == 0 {
                    v___x_1515_ = v___x_1512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
                    v___x_1515_ = v_reuseFailAlloc_1516_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1515_;
            }
            7 => {
                v___x_1522_ = lean_box(0);
                v___x_1523_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_1522_, v_a_1518_, v_m_1479_);
                if v_isShared_1521_ == 0 {
                    lean_ctor_set(v___x_1520_, 0, v___x_1523_);
                    v___x_1525_ = v___x_1520_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1526_, 0, v___x_1523_);
                    v___x_1525_ = v_reuseFailAlloc_1526_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f___redArg(
    mut v_inst_1529_: *mut LeanObject,
    mut v_x_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = l_Array_fromJson_x3f___redArg___closed__9;
    if lean_obj_tag(v_x_1530_) == 5 {
        let mut v_kvPairs_1532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
        v_kvPairs_1532_ = lean_ctor_get(v_x_1530_, 0);
        lean_inc(v_kvPairs_1532_);
        lean_dec_ref_known(v_x_1530_, 1);
        v___f_1533_ = lean_alloc_closure(
            l_Lean_NameMap_fromJson_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            4,
            1,
        );
        lean_closure_set(v___f_1533_, 0, v_inst_1529_);
        v___x_1534_ = lean_box(1);
        v___x_1535_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(
            v___x_1531_,
            v___f_1533_,
            v___x_1534_,
            v_kvPairs_1532_,
        );
        return v___x_1535_;
    } else {
        let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_1529_);
        v___x_1536_ = l_Lean_NameMap_fromJson_x3f___redArg___closed__0;
        v___x_1537_ = lean_unsigned_to_nat(80);
        v___x_1538_ = l_Lean_Json_pretty(v_x_1530_, v___x_1537_);
        v___x_1539_ = lean_string_append(v___x_1536_, v___x_1538_);
        lean_dec_ref(v___x_1538_);
        v___x_1540_ = l_Array_fromJson_x3f___redArg___closed__11;
        v___x_1541_ = lean_string_append(v___x_1539_, v___x_1540_);
        v___x_1542_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1542_, 0, v___x_1541_);
        return v___x_1542_;
    }
}
pub unsafe fn l_Lean_NameMap_fromJson_x3f(
    mut v_00_u03b1_1543_: *mut LeanObject,
    mut v_inst_1544_: *mut LeanObject,
    mut v_x_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = l_Lean_NameMap_fromJson_x3f___redArg(v_inst_1544_, v_x_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_instFromJsonNameMap___redArg(
    mut v_inst_1547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1548_ = lean_alloc_closure(l_Lean_NameMap_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1548_, 0, lean_box(0));
    lean_closure_set(v___x_1548_, 1, v_inst_1547_);
    return v___x_1548_;
}
pub unsafe fn l_Lean_instFromJsonNameMap(
    mut v_00_u03b1_1549_: *mut LeanObject,
    mut v_inst_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = lean_alloc_closure(l_Lean_NameMap_fromJson_x3f as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1551_, 0, lean_box(0));
    lean_closure_set(v___x_1551_, 1, v_inst_1550_);
    return v___x_1551_;
}
pub unsafe fn l_Lean_NameMap_toJson___redArg___lam__0(
    mut v_inst_1553_: *mut LeanObject,
    mut v_n_1554_: *mut LeanObject,
    mut v_k_1555_: *mut LeanObject,
    mut v_v_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: u8 = 0;
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = l_Lean_NameMap_toJson___redArg___lam__0___closed__0;
    v___x_1558_ = 1;
    v___x_1559_ = l_Lean_Name_toString(v_k_1555_, v___x_1558_);
    v___x_1560_ = lean_apply_1(v_inst_1553_, v_v_1556_);
    v___x_1561_ = l_Std_DTreeMap_Internal_Impl_insert_x21___redArg(
        v___x_1557_,
        v___x_1559_,
        v___x_1560_,
        v_n_1554_,
    );
    return v___x_1561_;
}
pub unsafe fn l_Lean_NameMap_toJson___redArg(
    mut v_inst_1562_: *mut LeanObject,
    mut v_m_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    v___f_1564_ = lean_alloc_closure(
        l_Lean_NameMap_toJson___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1564_, 0, v_inst_1562_);
    v___x_1565_ = lean_box(1);
    v___x_1566_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1564_, v___x_1565_, v_m_1563_);
    v___x_1567_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_1567_, 0, v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn l_Lean_NameMap_toJson(
    mut v_00_u03b1_1568_: *mut LeanObject,
    mut v_inst_1569_: *mut LeanObject,
    mut v_m_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    v___x_1571_ = l_Lean_NameMap_toJson___redArg(v_inst_1569_, v_m_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lean_instToJsonNameMap___redArg(
    mut v_inst_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ = lean_alloc_closure(l_Lean_NameMap_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1573_, 0, lean_box(0));
    lean_closure_set(v___x_1573_, 1, v_inst_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_instToJsonNameMap(
    mut v_00_u03b1_1574_: *mut LeanObject,
    mut v_inst_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_alloc_closure(l_Lean_NameMap_toJson as *mut core::ffi::c_void, 3, 2);
    lean_closure_set(v___x_1576_, 0, lean_box(0));
    lean_closure_set(v___x_1576_, 1, v_inst_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_bignumFromJson_x3f(mut v_j_1578_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1583_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_a_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1591_: u8 = 0;
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_1578_);
                v___x_1579_ = l_Lean_Json_getStr_x3f(v_j_1578_);
                if lean_obj_tag(v___x_1579_) == 0 {
                    lean_dec(v_j_1578_);
                    v_a_1580_ = lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1587_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1587_ == 0 {
                        v___x_1582_ = v___x_1579_;
                        v_isShared_1583_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1580_);
                        lean_dec(v___x_1579_);
                        v___x_1582_ = lean_box(0);
                        v_isShared_1583_ = v_isSharedCheck_1587_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1588_ = lean_ctor_get(v___x_1579_, 0);
                    v_isSharedCheck_1606_ = (!lean_is_exclusive(v___x_1579_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v___x_1590_ = v___x_1579_;
                        v_isShared_1591_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1588_);
                        lean_dec(v___x_1579_);
                        v___x_1590_ = lean_box(0);
                        v_isShared_1591_ = v_isSharedCheck_1606_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1583_ == 0 {
                    v___x_1585_ = v___x_1582_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
                    v___x_1585_ = v_reuseFailAlloc_1586_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1585_;
            }
            3 => {
                v___x_1592_ = l_Lean_Syntax_decodeNatLitVal_x3f(v_a_1588_);
                lean_dec(v_a_1588_);
                if lean_obj_tag(v___x_1592_) == 1 {
                    lean_dec(v_j_1578_);
                    v_val_1593_ = lean_ctor_get(v___x_1592_, 0);
                    lean_inc(v_val_1593_);
                    lean_dec_ref_known(v___x_1592_, 1);
                    if v_isShared_1591_ == 0 {
                        lean_ctor_set(v___x_1590_, 0, v_val_1593_);
                        v___x_1595_ = v___x_1590_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_val_1593_);
                        v___x_1595_ = v_reuseFailAlloc_1596_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1592_);
                    v___x_1597_ = l_Lean_bignumFromJson_x3f___closed__0;
                    v___x_1598_ = lean_unsigned_to_nat(80);
                    v___x_1599_ = l_Lean_Json_pretty(v_j_1578_, v___x_1598_);
                    v___x_1600_ = lean_string_append(v___x_1597_, v___x_1599_);
                    lean_dec_ref(v___x_1599_);
                    v___x_1601_ = l_Array_fromJson_x3f___redArg___closed__11;
                    v___x_1602_ = lean_string_append(v___x_1600_, v___x_1601_);
                    if v_isShared_1591_ == 0 {
                        lean_ctor_set_tag(v___x_1590_, 0);
                        lean_ctor_set(v___x_1590_, 0, v___x_1602_);
                        v___x_1604_ = v___x_1590_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1605_, 0, v___x_1602_);
                        v___x_1604_ = v_reuseFailAlloc_1605_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1595_;
            }
            5 => {
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_bignumToJson(mut v_n_1607_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    v___x_1608_ = l_Nat_reprFast(v_n_1607_);
    v___x_1609_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1609_, 0, v___x_1608_);
    return v___x_1609_;
}
pub unsafe fn _init_l_USize_fromJson_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ = l_System_Platform_numBits;
    v___x_1611_ = lean_unsigned_to_nat(2);
    v___x_1612_ = lean_nat_pow(v___x_1611_, v___x_1610_);
    return v___x_1612_;
}
pub unsafe fn l_USize_fromJson_x3f(mut v_j_1615_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1624_: u8 = 0;
    let mut v_a_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1628_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: usize = 0;
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_1615_);
                v___x_1616_ = l_Lean_bignumFromJson_x3f(v_j_1615_);
                if lean_obj_tag(v___x_1616_) == 0 {
                    lean_dec(v_j_1615_);
                    v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
                    v_isSharedCheck_1624_ = (!lean_is_exclusive(v___x_1616_)) as u8;
                    if v_isSharedCheck_1624_ == 0 {
                        v___x_1619_ = v___x_1616_;
                        v_isShared_1620_ = v_isSharedCheck_1624_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1617_);
                        lean_dec(v___x_1616_);
                        v___x_1619_ = lean_box(0);
                        v_isShared_1620_ = v_isSharedCheck_1624_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1625_ = lean_ctor_get(v___x_1616_, 0);
                    v_isSharedCheck_1645_ = (!lean_is_exclusive(v___x_1616_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1627_ = v___x_1616_;
                        v_isShared_1628_ = v_isSharedCheck_1645_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1625_);
                        lean_dec(v___x_1616_);
                        v___x_1627_ = lean_box(0);
                        v_isShared_1628_ = v_isSharedCheck_1645_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1620_ == 0 {
                    v___x_1622_ = v___x_1619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1623_, 0, v_a_1617_);
                    v___x_1622_ = v_reuseFailAlloc_1623_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1622_;
            }
            3 => {
                v___x_1629_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_USize_fromJson_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_USize_fromJson_x3f___closed__0_once),
                    _init_l_USize_fromJson_x3f___closed__0,
                );
                v___x_1630_ = lean_nat_dec_le(v___x_1629_, v_a_1625_);
                if v___x_1630_ == 0 {
                    lean_dec(v_j_1615_);
                    v___x_1631_ = lean_usize_of_nat(v_a_1625_);
                    lean_dec(v_a_1625_);
                    v___x_1632_ = lean_box_usize(v___x_1631_);
                    if v_isShared_1628_ == 0 {
                        lean_ctor_set(v___x_1627_, 0, v___x_1632_);
                        v___x_1634_ = v___x_1627_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1635_, 0, v___x_1632_);
                        v___x_1634_ = v_reuseFailAlloc_1635_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1625_);
                    v___x_1636_ = l_USize_fromJson_x3f___closed__1;
                    v___x_1637_ = lean_unsigned_to_nat(80);
                    v___x_1638_ = l_Lean_Json_pretty(v_j_1615_, v___x_1637_);
                    v___x_1639_ = lean_string_append(v___x_1636_, v___x_1638_);
                    lean_dec_ref(v___x_1638_);
                    v___x_1640_ = l_USize_fromJson_x3f___closed__2;
                    v___x_1641_ = lean_string_append(v___x_1639_, v___x_1640_);
                    if v_isShared_1628_ == 0 {
                        lean_ctor_set_tag(v___x_1627_, 0);
                        lean_ctor_set(v___x_1627_, 0, v___x_1641_);
                        v___x_1643_ = v___x_1627_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
                        v___x_1643_ = v_reuseFailAlloc_1644_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1634_;
            }
            5 => {
                return v___x_1643_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUSize___lam__0(mut v_v_1648_: usize) -> *mut LeanObject {
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1649_ = lean_usize_to_nat(v_v_1648_);
    v___x_1650_ = l_Lean_bignumToJson(v___x_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Lean_instToJsonUSize___lam__0___boxed(
    mut v_v_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1652_: usize = 0;
    let mut v_res_1653_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1652_ = lean_unbox_usize(v_v_1651_);
    lean_dec(v_v_1651_);
    v_res_1653_ = l_Lean_instToJsonUSize___lam__0(v_v_boxed_1652_);
    return v_res_1653_;
}
pub unsafe fn _init_l_UInt64_fromJson_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    v___x_1656_ = lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_1656_;
}
pub unsafe fn l_UInt64_fromJson_x3f(mut v_j_1658_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1663_: u8 = 0;
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: u64 = 0;
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1688_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_j_1658_);
                v___x_1659_ = l_Lean_bignumFromJson_x3f(v_j_1658_);
                if lean_obj_tag(v___x_1659_) == 0 {
                    lean_dec(v_j_1658_);
                    v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1667_ = (!lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1662_ = v___x_1659_;
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1660_);
                        lean_dec(v___x_1659_);
                        v___x_1662_ = lean_box(0);
                        v_isShared_1663_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1668_ = lean_ctor_get(v___x_1659_, 0);
                    v_isSharedCheck_1688_ = (!lean_is_exclusive(v___x_1659_)) as u8;
                    if v_isSharedCheck_1688_ == 0 {
                        v___x_1670_ = v___x_1659_;
                        v_isShared_1671_ = v_isSharedCheck_1688_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1668_);
                        lean_dec(v___x_1659_);
                        v___x_1670_ = lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1688_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1663_ == 0 {
                    v___x_1665_ = v___x_1662_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1666_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
                    v___x_1665_ = v_reuseFailAlloc_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1665_;
            }
            3 => {
                v___x_1672_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_UInt64_fromJson_x3f___closed__0),
                    core::ptr::addr_of_mut!(l_UInt64_fromJson_x3f___closed__0_once),
                    _init_l_UInt64_fromJson_x3f___closed__0,
                );
                v___x_1673_ = lean_nat_dec_le(v___x_1672_, v_a_1668_);
                if v___x_1673_ == 0 {
                    lean_dec(v_j_1658_);
                    v___x_1674_ = lean_uint64_of_nat(v_a_1668_);
                    lean_dec(v_a_1668_);
                    v___x_1675_ = lean_box_uint64(v___x_1674_);
                    if v_isShared_1671_ == 0 {
                        lean_ctor_set(v___x_1670_, 0, v___x_1675_);
                        v___x_1677_ = v___x_1670_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
                        v___x_1677_ = v_reuseFailAlloc_1678_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1668_);
                    v___x_1679_ = l_USize_fromJson_x3f___closed__1;
                    v___x_1680_ = lean_unsigned_to_nat(80);
                    v___x_1681_ = l_Lean_Json_pretty(v_j_1658_, v___x_1680_);
                    v___x_1682_ = lean_string_append(v___x_1679_, v___x_1681_);
                    lean_dec_ref(v___x_1681_);
                    v___x_1683_ = l_UInt64_fromJson_x3f___closed__1;
                    v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
                    if v_isShared_1671_ == 0 {
                        lean_ctor_set_tag(v___x_1670_, 0);
                        lean_ctor_set(v___x_1670_, 0, v___x_1684_);
                        v___x_1686_ = v___x_1670_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1684_);
                        v___x_1686_ = v_reuseFailAlloc_1687_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1677_;
            }
            5 => {
                return v___x_1686_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instToJsonUInt64___lam__0(mut v_v_1691_: u64) -> *mut LeanObject {
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    v___x_1692_ = lean_uint64_to_nat(v_v_1691_);
    v___x_1693_ = l_Lean_bignumToJson(v___x_1692_);
    return v___x_1693_;
}
pub unsafe fn l_Lean_instToJsonUInt64___lam__0___boxed(
    mut v_v_1694_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1695_: u64 = 0;
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1695_ = lean_unbox_uint64(v_v_1694_);
    lean_dec_ref(v_v_1694_);
    v_res_1696_ = l_Lean_instToJsonUInt64___lam__0(v_v_boxed_1695_);
    return v_res_1696_;
}
pub unsafe fn l_Float_toJson(mut v_x_1699_: f64) -> *mut LeanObject {
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1704_: u8 = 0;
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_val_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1700_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_1699_);
                if lean_obj_tag(v___x_1700_) == 0 {
                    v_val_1701_ = lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1708_ = (!lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1703_ = v___x_1700_;
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1701_);
                        lean_dec(v___x_1700_);
                        v___x_1703_ = lean_box(0);
                        v_isShared_1704_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_val_1709_ = lean_ctor_get(v___x_1700_, 0);
                    v_isSharedCheck_1716_ = (!lean_is_exclusive(v___x_1700_)) as u8;
                    if v_isSharedCheck_1716_ == 0 {
                        v___x_1711_ = v___x_1700_;
                        v_isShared_1712_ = v_isSharedCheck_1716_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1709_);
                        lean_dec(v___x_1700_);
                        v___x_1711_ = lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1716_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1704_ == 0 {
                    lean_ctor_set_tag(v___x_1703_, 3);
                    v___x_1706_ = v___x_1703_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_val_1701_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                if v_isShared_1712_ == 0 {
                    lean_ctor_set_tag(v___x_1711_, 2);
                    v___x_1714_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1715_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_val_1709_);
                    v___x_1714_ = v_reuseFailAlloc_1715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Float_toJson___boxed(mut v_x_1717_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_boxed_1718_: f64 = 0.0;
    let mut v_res_1719_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1718_ = lean_unbox_float(v_x_1717_);
    lean_dec_ref(v_x_1717_);
    v_res_1719_ = l_Float_toJson(v_x_boxed_1718_);
    return v_res_1719_;
}
pub unsafe fn l_Float_fromJson_x3f(mut v_x_1728_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1734_: u8 = 0;
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: u8 = 0;
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: f64 = 0.0;
    let mut v___x_1744_: f64 = 0.0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: f64 = 0.0;
    let mut v___x_1752_: f64 = 0.0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: f64 = 0.0;
    let mut v___x_1755_: f64 = 0.0;
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: f64 = 0.0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: f64 = 0.0;
    let mut v___x_1765_: f64 = 0.0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_n_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1775_: f64 = 0.0;
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1728_) {
                3 => {
                    v_s_1731_ = lean_ctor_get(v_x_1728_, 0);
                    v_isSharedCheck_1770_ = (!lean_is_exclusive(v_x_1728_)) as u8;
                    if v_isSharedCheck_1770_ == 0 {
                        v___x_1733_ = v_x_1728_;
                        v_isShared_1734_ = v_isSharedCheck_1770_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_s_1731_);
                        lean_dec(v_x_1728_);
                        v___x_1733_ = lean_box(0);
                        v_isShared_1734_ = v_isSharedCheck_1770_;
                        state = 2;
                        continue;
                    }
                }
                2 => {
                    v_n_1771_ = lean_ctor_get(v_x_1728_, 0);
                    v_isSharedCheck_1780_ = (!lean_is_exclusive(v_x_1728_)) as u8;
                    if v_isSharedCheck_1780_ == 0 {
                        v___x_1773_ = v_x_1728_;
                        v_isShared_1774_ = v_isSharedCheck_1780_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_n_1771_);
                        lean_dec(v_x_1728_);
                        v___x_1773_ = lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1780_;
                        state = 6;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_x_1728_);
                    state = 1;
                    continue;
                }
            },
            1 => {
                v___x_1730_ = l_Float_fromJson_x3f___closed__1;
                return v___x_1730_;
            }
            2 => {
                v___x_1735_ = l_Float_fromJson_x3f___closed__2;
                v___x_1736_ = lean_string_dec_eq(v_s_1731_, v___x_1735_);
                if v___x_1736_ == 0 {
                    v___x_1737_ = l_Float_fromJson_x3f___closed__3;
                    v___x_1738_ = lean_string_dec_eq(v_s_1731_, v___x_1737_);
                    if v___x_1738_ == 0 {
                        v___x_1739_ = l_Float_fromJson_x3f___closed__4;
                        v___x_1740_ = lean_string_dec_eq(v_s_1731_, v___x_1739_);
                        lean_dec_ref(v_s_1731_);
                        if v___x_1740_ == 0 {
                            lean_del_object(v___x_1733_);
                            state = 1;
                            continue;
                        } else {
                            v___x_1741_ = lean_unsigned_to_nat(0);
                            v___x_1742_ = lean_unsigned_to_nat(1);
                            v___x_1743_ =
                                l_Float_ofScientific(v___x_1741_, v___x_1740_, v___x_1742_);
                            v___x_1744_ = lean_float_div(v___x_1743_, v___x_1743_);
                            v___x_1745_ = lean_box_float(v___x_1744_);
                            if v_isShared_1734_ == 0 {
                                lean_ctor_set_tag(v___x_1733_, 1);
                                lean_ctor_set(v___x_1733_, 0, v___x_1745_);
                                v___x_1747_ = v___x_1733_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1748_, 0, v___x_1745_);
                                v___x_1747_ = v_reuseFailAlloc_1748_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_s_1731_);
                        v___x_1749_ = lean_unsigned_to_nat(10);
                        v___x_1750_ = lean_unsigned_to_nat(1);
                        v___x_1751_ = l_Float_ofScientific(v___x_1749_, v___x_1738_, v___x_1750_);
                        v___x_1752_ = lean_float_negate(v___x_1751_);
                        v___x_1753_ = lean_unsigned_to_nat(0);
                        v___x_1754_ = l_Float_ofScientific(v___x_1753_, v___x_1738_, v___x_1750_);
                        v___x_1755_ = lean_float_div(v___x_1752_, v___x_1754_);
                        v___x_1756_ = lean_box_float(v___x_1755_);
                        if v_isShared_1734_ == 0 {
                            lean_ctor_set_tag(v___x_1733_, 1);
                            lean_ctor_set(v___x_1733_, 0, v___x_1756_);
                            v___x_1758_ = v___x_1733_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1759_, 0, v___x_1756_);
                            v___x_1758_ = v_reuseFailAlloc_1759_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_s_1731_);
                    v___x_1760_ = lean_unsigned_to_nat(10);
                    v___x_1761_ = lean_unsigned_to_nat(1);
                    v___x_1762_ = l_Float_ofScientific(v___x_1760_, v___x_1736_, v___x_1761_);
                    v___x_1763_ = lean_unsigned_to_nat(0);
                    v___x_1764_ = l_Float_ofScientific(v___x_1763_, v___x_1736_, v___x_1761_);
                    v___x_1765_ = lean_float_div(v___x_1762_, v___x_1764_);
                    v___x_1766_ = lean_box_float(v___x_1765_);
                    if v_isShared_1734_ == 0 {
                        lean_ctor_set_tag(v___x_1733_, 1);
                        lean_ctor_set(v___x_1733_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1733_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1747_;
            }
            4 => {
                return v___x_1758_;
            }
            5 => {
                return v___x_1768_;
            }
            6 => {
                v___x_1775_ = l_Lean_JsonNumber_toFloat(v_n_1771_);
                v___x_1776_ = lean_box_float(v___x_1775_);
                if v_isShared_1774_ == 0 {
                    lean_ctor_set_tag(v___x_1773_, 1);
                    lean_ctor_set(v___x_1773_, 0, v___x_1776_);
                    v___x_1778_ = v___x_1773_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1776_);
                    v___x_1778_ = v_reuseFailAlloc_1779_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Structured_fromJson_x3f(
    mut v_x_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1793_: u8 = 0;
    let mut v_kvPairs_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1784_) {
                4 => {
                    v_elems_1785_ = lean_ctor_get(v_x_1784_, 0);
                    v_isSharedCheck_1793_ = (!lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1793_ == 0 {
                        v___x_1787_ = v_x_1784_;
                        v_isShared_1788_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_elems_1785_);
                        lean_dec(v_x_1784_);
                        v___x_1787_ = lean_box(0);
                        v_isShared_1788_ = v_isSharedCheck_1793_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_kvPairs_1794_ = lean_ctor_get(v_x_1784_, 0);
                    v_isSharedCheck_1802_ = (!lean_is_exclusive(v_x_1784_)) as u8;
                    if v_isSharedCheck_1802_ == 0 {
                        v___x_1796_ = v_x_1784_;
                        v_isShared_1797_ = v_isSharedCheck_1802_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_kvPairs_1794_);
                        lean_dec(v_x_1784_);
                        v___x_1796_ = lean_box(0);
                        v_isShared_1797_ = v_isSharedCheck_1802_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_1803_ = l_Lean_Json_Structured_fromJson_x3f___closed__0;
                    v___x_1804_ = lean_unsigned_to_nat(80);
                    v___x_1805_ = l_Lean_Json_pretty(v_x_1784_, v___x_1804_);
                    v___x_1806_ = lean_string_append(v___x_1803_, v___x_1805_);
                    lean_dec_ref(v___x_1805_);
                    v___x_1807_ = l_Array_fromJson_x3f___redArg___closed__11;
                    v___x_1808_ = lean_string_append(v___x_1806_, v___x_1807_);
                    v___x_1809_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1809_, 0, v___x_1808_);
                    return v___x_1809_;
                }
            },
            1 => {
                if v_isShared_1788_ == 0 {
                    lean_ctor_set_tag(v___x_1787_, 0);
                    v___x_1790_ = v___x_1787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_elems_1785_);
                    v___x_1790_ = v_reuseFailAlloc_1792_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1791_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1791_, 0, v___x_1790_);
                return v___x_1791_;
            }
            3 => {
                if v_isShared_1797_ == 0 {
                    lean_ctor_set_tag(v___x_1796_, 1);
                    v___x_1799_ = v___x_1796_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_kvPairs_1794_);
                    v___x_1799_ = v_reuseFailAlloc_1801_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1800_, 0, v___x_1799_);
                return v___x_1800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_Structured_toJson(mut v_x_1812_: *mut LeanObject) -> *mut LeanObject {
    let mut v_elems_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1816_: u8 = 0;
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1820_: u8 = 0;
    let mut v_kvPairs_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1824_: u8 = 0;
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1812_) == 0 {
                    v_elems_1813_ = lean_ctor_get(v_x_1812_, 0);
                    v_isSharedCheck_1820_ = (!lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1820_ == 0 {
                        v___x_1815_ = v_x_1812_;
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_elems_1813_);
                        lean_dec(v_x_1812_);
                        v___x_1815_ = lean_box(0);
                        v_isShared_1816_ = v_isSharedCheck_1820_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_kvPairs_1821_ = lean_ctor_get(v_x_1812_, 0);
                    v_isSharedCheck_1828_ = (!lean_is_exclusive(v_x_1812_)) as u8;
                    if v_isSharedCheck_1828_ == 0 {
                        v___x_1823_ = v_x_1812_;
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_kvPairs_1821_);
                        lean_dec(v_x_1812_);
                        v___x_1823_ = lean_box(0);
                        v_isShared_1824_ = v_isSharedCheck_1828_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1816_ == 0 {
                    lean_ctor_set_tag(v___x_1815_, 4);
                    v___x_1818_ = v___x_1815_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1819_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_elems_1813_);
                    v___x_1818_ = v_reuseFailAlloc_1819_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1818_;
            }
            3 => {
                if v_isShared_1824_ == 0 {
                    lean_ctor_set_tag(v___x_1823_, 5);
                    v___x_1826_ = v___x_1823_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1827_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_kvPairs_1821_);
                    v___x_1826_ = v_reuseFailAlloc_1827_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_toStructured_x3f___redArg(
    mut v_inst_1831_: *mut LeanObject,
    mut v_v_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    v___x_1833_ = lean_apply_1(v_inst_1831_, v_v_1832_);
    v___x_1834_ = l_Lean_Json_Structured_fromJson_x3f(v___x_1833_);
    return v___x_1834_;
}
pub unsafe fn l_Lean_Json_toStructured_x3f(
    mut v_00_u03b1_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
    mut v_v_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ = l_Lean_Json_toStructured_x3f___redArg(v_inst_1836_, v_v_1837_);
    return v___x_1838_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___redArg(
    mut v_j_1839_: *mut LeanObject,
    mut v_inst_1840_: *mut LeanObject,
    mut v_k_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1842_ = l_Lean_Json_getObjValD(v_j_1839_, v_k_1841_);
    v___x_1843_ = lean_apply_1(v_inst_1840_, v___x_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___redArg___boxed(
    mut v_j_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_k_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1847_: *mut LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1844_, v_inst_1845_, v_k_1846_);
    lean_dec_ref(v_k_1846_);
    return v_res_1847_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f(
    mut v_j_1848_: *mut LeanObject,
    mut v_00_u03b1_1849_: *mut LeanObject,
    mut v_inst_1850_: *mut LeanObject,
    mut v_k_1851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = l_Lean_Json_getObjValAs_x3f___redArg(v_j_1848_, v_inst_1850_, v_k_1851_);
    return v___x_1852_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___boxed(
    mut v_j_1853_: *mut LeanObject,
    mut v_00_u03b1_1854_: *mut LeanObject,
    mut v_inst_1855_: *mut LeanObject,
    mut v_k_1856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1857_: *mut LeanObject = core::ptr::null_mut();
    v_res_1857_ = l_Lean_Json_getObjValAs_x3f(v_j_1853_, v_00_u03b1_1854_, v_inst_1855_, v_k_1856_);
    lean_dec_ref(v_k_1856_);
    return v_res_1857_;
}
pub unsafe fn l_Lean_Json_setObjValAs_x21___redArg(
    mut v_j_1858_: *mut LeanObject,
    mut v_inst_1859_: *mut LeanObject,
    mut v_k_1860_: *mut LeanObject,
    mut v_v_1861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = lean_apply_1(v_inst_1859_, v_v_1861_);
    v___x_1863_ = l_Lean_Json_setObjVal_x21(v_j_1858_, v_k_1860_, v___x_1862_);
    return v___x_1863_;
}
pub unsafe fn l_Lean_Json_setObjValAs_x21(
    mut v_j_1864_: *mut LeanObject,
    mut v_00_u03b1_1865_: *mut LeanObject,
    mut v_inst_1866_: *mut LeanObject,
    mut v_k_1867_: *mut LeanObject,
    mut v_v_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    v___x_1869_ =
        l_Lean_Json_setObjValAs_x21___redArg(v_j_1864_, v_inst_1866_, v_k_1867_, v_v_1868_);
    return v___x_1869_;
}
pub unsafe fn l_Lean_Json_opt___redArg(
    mut v_inst_1870_: *mut LeanObject,
    mut v_k_1871_: *mut LeanObject,
    mut v_x_1872_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1872_) == 0 {
        let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_k_1871_);
        lean_dec_ref(v_inst_1870_);
        v___x_1873_ = lean_box(0);
        return v___x_1873_;
    } else {
        let mut v_val_1874_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
        v_val_1874_ = lean_ctor_get(v_x_1872_, 0);
        lean_inc(v_val_1874_);
        lean_dec_ref_known(v_x_1872_, 1);
        v___x_1875_ = lean_apply_1(v_inst_1870_, v_val_1874_);
        v___x_1876_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1876_, 0, v_k_1871_);
        lean_ctor_set(v___x_1876_, 1, v___x_1875_);
        v___x_1877_ = lean_box(0);
        v___x_1878_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_1878_, 0, v___x_1876_);
        lean_ctor_set(v___x_1878_, 1, v___x_1877_);
        return v___x_1878_;
    }
}
pub unsafe fn l_Lean_Json_opt(
    mut v_00_u03b1_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_k_1881_: *mut LeanObject,
    mut v_x_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_Json_opt___redArg(v_inst_1880_, v_k_1881_, v_x_1882_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_Json_getTag_x3f(mut v_x_1884_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1888_: u8 = 0;
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1892_: u8 = 0;
    let mut v_kvPairs_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1884_) {
                3 => {
                    v_s_1885_ = lean_ctor_get(v_x_1884_, 0);
                    v_isSharedCheck_1892_ = (!lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1892_ == 0 {
                        v___x_1887_ = v_x_1884_;
                        v_isShared_1888_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_1885_);
                        lean_dec(v_x_1884_);
                        v___x_1887_ = lean_box(0);
                        v_isShared_1888_ = v_isSharedCheck_1892_;
                        state = 1;
                        continue;
                    }
                }
                5 => {
                    v_kvPairs_1893_ = lean_ctor_get(v_x_1884_, 0);
                    lean_inc(v_kvPairs_1893_);
                    lean_dec_ref_known(v_x_1884_, 1);
                    if lean_obj_tag(v_kvPairs_1893_) == 0 {
                        v_size_1900_ = lean_ctor_get(v_kvPairs_1893_, 0);
                        lean_inc(v_size_1900_);
                        v___y_1895_ = v_size_1900_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1901_ = lean_unsigned_to_nat(0);
                        v___y_1895_ = v___x_1901_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    lean_dec(v_x_1884_);
                    v___x_1902_ = lean_box(0);
                    return v___x_1902_;
                }
            },
            1 => {
                if v_isShared_1888_ == 0 {
                    lean_ctor_set_tag(v___x_1887_, 1);
                    v___x_1890_ = v___x_1887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_s_1885_);
                    v___x_1890_ = v_reuseFailAlloc_1891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1890_;
            }
            3 => {
                v___x_1896_ = lean_unsigned_to_nat(1);
                v___x_1897_ = lean_nat_dec_eq(v___y_1895_, v___x_1896_);
                lean_dec(v___y_1895_);
                if v___x_1897_ == 0 {
                    lean_dec(v_kvPairs_1893_);
                    v___x_1898_ = lean_box(0);
                    return v___x_1898_;
                } else {
                    v___x_1899_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_kvPairs_1893_);
                    lean_dec(v_kvPairs_1893_);
                    return v___x_1899_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(
    mut v_a_1903_: *mut LeanObject,
    mut v_as_1904_: *mut LeanObject,
    mut v_sz_1905_: usize,
    mut v_i_1906_: usize,
    mut v_b_1907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut v_a_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: usize = 0;
    let mut v___x_1924_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1908_ = lean_usize_dec_lt(v_i_1906_, v_sz_1905_);
                if v___x_1908_ == 0 {
                    lean_dec(v_a_1903_);
                    v___x_1909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1909_, 0, v_b_1907_);
                    return v___x_1909_;
                } else {
                    v_a_1910_ = lean_array_uget_borrowed(v_as_1904_, v_i_1906_);
                    v___x_1911_ = l_Lean_Name_getString_x21(v_a_1910_);
                    lean_inc(v_a_1903_);
                    v___x_1912_ = l_Lean_Json_getObjVal_x3f(v_a_1903_, v___x_1911_);
                    lean_dec_ref(v___x_1911_);
                    if lean_obj_tag(v___x_1912_) == 0 {
                        lean_dec_ref(v_b_1907_);
                        lean_dec(v_a_1903_);
                        v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
                        v_isSharedCheck_1920_ = (!lean_is_exclusive(v___x_1912_)) as u8;
                        if v_isSharedCheck_1920_ == 0 {
                            v___x_1915_ = v___x_1912_;
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1913_);
                            lean_dec(v___x_1912_);
                            v___x_1915_ = lean_box(0);
                            v_isShared_1916_ = v_isSharedCheck_1920_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1921_ = lean_ctor_get(v___x_1912_, 0);
                        lean_inc(v_a_1921_);
                        lean_dec_ref_known(v___x_1912_, 1);
                        v___x_1922_ = lean_array_push(v_b_1907_, v_a_1921_);
                        v___x_1923_ = 1usize;
                        v___x_1924_ = lean_usize_add(v_i_1906_, v___x_1923_);
                        v_i_1906_ = v___x_1924_;
                        v_b_1907_ = v___x_1922_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1916_ == 0 {
                    v___x_1918_ = v___x_1915_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0___boxed(
    mut v_a_1926_: *mut LeanObject,
    mut v_as_1927_: *mut LeanObject,
    mut v_sz_1928_: *mut LeanObject,
    mut v_i_1929_: *mut LeanObject,
    mut v_b_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1931_: usize = 0;
    let mut v_i_boxed_1932_: usize = 0;
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1931_ = lean_unbox_usize(v_sz_1928_);
    lean_dec(v_sz_1928_);
    v_i_boxed_1932_ = lean_unbox_usize(v_i_1929_);
    lean_dec(v_i_1929_);
    v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_1926_, v_as_1927_, v_sz_boxed_1931_, v_i_boxed_1932_, v_b_1930_);
    lean_dec_ref(v_as_1927_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_Json_parseTagged(
    mut v_json_1941_: *mut LeanObject,
    mut v_tag_1942_: *mut LeanObject,
    mut v_nFields_1943_: *mut LeanObject,
    mut v_fieldNames_x3f_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1951_: u8 = 0;
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1955_: u8 = 0;
    let mut v_a_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1968_: u8 = 0;
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1979_: u8 = 0;
    let mut v_unused_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1986_: u8 = 0;
    let mut v_a_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fields_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1990_: usize = 0;
    let mut v___x_1991_: usize = 0;
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1997_: u8 = 0;
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2001_: u8 = 0;
    let mut v_a_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2005_: u8 = 0;
    let mut v___x_2006_: u8 = 0;
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2016_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1945_ = lean_unsigned_to_nat(0);
                v___x_1946_ = lean_nat_dec_eq(v_nFields_1943_, v___x_1945_);
                if v___x_1946_ == 0 {
                    v___x_1947_ = l_Lean_Json_getObjVal_x3f(v_json_1941_, v_tag_1942_);
                    if lean_obj_tag(v___x_1947_) == 0 {
                        lean_dec(v_nFields_1943_);
                        v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
                        v_isSharedCheck_1955_ = (!lean_is_exclusive(v___x_1947_)) as u8;
                        if v_isSharedCheck_1955_ == 0 {
                            v___x_1950_ = v___x_1947_;
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1948_);
                            lean_dec(v___x_1947_);
                            v___x_1950_ = lean_box(0);
                            v_isShared_1951_ = v_isSharedCheck_1955_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v_fieldNames_x3f_1944_) == 0 {
                            v_a_1956_ = lean_ctor_get(v___x_1947_, 0);
                            v_isSharedCheck_1986_ = (!lean_is_exclusive(v___x_1947_)) as u8;
                            if v_isSharedCheck_1986_ == 0 {
                                v___x_1958_ = v___x_1947_;
                                v_isShared_1959_ = v_isSharedCheck_1986_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_1956_);
                                lean_dec(v___x_1947_);
                                v___x_1958_ = lean_box(0);
                                v_isShared_1959_ = v_isSharedCheck_1986_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_nFields_1943_);
                            v_a_1987_ = lean_ctor_get(v___x_1947_, 0);
                            lean_inc(v_a_1987_);
                            lean_dec_ref_known(v___x_1947_, 1);
                            v_val_1988_ = lean_ctor_get(v_fieldNames_x3f_1944_, 0);
                            v_fields_1989_ = l_Lean_Json_parseTagged___closed__2;
                            v_sz_1990_ = lean_array_size(v_val_1988_);
                            v___x_1991_ = 0usize;
                            v___x_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Json_parseTagged_spec__0(v_a_1987_, v_val_1988_, v_sz_1990_, v___x_1991_, v_fields_1989_);
                            return v___x_1992_;
                        }
                    }
                } else {
                    lean_dec(v_nFields_1943_);
                    v___x_1993_ = l_Lean_Json_getStr_x3f(v_json_1941_);
                    if lean_obj_tag(v___x_1993_) == 0 {
                        v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
                        v_isSharedCheck_2001_ = (!lean_is_exclusive(v___x_1993_)) as u8;
                        if v_isSharedCheck_2001_ == 0 {
                            v___x_1996_ = v___x_1993_;
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1994_);
                            lean_dec(v___x_1993_);
                            v___x_1996_ = lean_box(0);
                            v_isShared_1997_ = v_isSharedCheck_2001_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_2002_ = lean_ctor_get(v___x_1993_, 0);
                        v_isSharedCheck_2016_ = (!lean_is_exclusive(v___x_1993_)) as u8;
                        if v_isSharedCheck_2016_ == 0 {
                            v___x_2004_ = v___x_1993_;
                            v_isShared_2005_ = v_isSharedCheck_2016_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2002_);
                            lean_dec(v___x_1993_);
                            v___x_2004_ = lean_box(0);
                            v_isShared_2005_ = v_isSharedCheck_2016_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1951_ == 0 {
                    v___x_1953_ = v___x_1950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1948_);
                    v___x_1953_ = v_reuseFailAlloc_1954_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1953_;
            }
            3 => {
                v___x_1960_ = lean_unsigned_to_nat(1);
                v___x_1961_ = lean_nat_dec_eq(v_nFields_1943_, v___x_1960_);
                if v___x_1961_ == 0 {
                    lean_del_object(v___x_1958_);
                    v___x_1962_ = l_Lean_Json_getArr_x3f(v_a_1956_);
                    if lean_obj_tag(v___x_1962_) == 0 {
                        lean_dec(v_nFields_1943_);
                        return v___x_1962_;
                    } else {
                        v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
                        lean_inc(v_a_1963_);
                        v___x_1964_ = lean_array_get_size(v_a_1963_);
                        lean_dec(v_a_1963_);
                        v___x_1965_ = lean_nat_dec_eq(v___x_1964_, v_nFields_1943_);
                        if v___x_1965_ == 0 {
                            v_isSharedCheck_1979_ = (!lean_is_exclusive(v___x_1962_)) as u8;
                            if v_isSharedCheck_1979_ == 0 {
                                v_unused_1980_ = lean_ctor_get(v___x_1962_, 0);
                                lean_dec(v_unused_1980_);
                                v___x_1967_ = v___x_1962_;
                                v_isShared_1968_ = v_isSharedCheck_1979_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_1962_);
                                v___x_1967_ = lean_box(0);
                                v_isShared_1968_ = v_isSharedCheck_1979_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_nFields_1943_);
                            return v___x_1962_;
                        }
                    }
                } else {
                    lean_dec(v_nFields_1943_);
                    v___x_1981_ = lean_mk_empty_array_with_capacity(v___x_1960_);
                    v___x_1982_ = lean_array_push(v___x_1981_, v_a_1956_);
                    if v_isShared_1959_ == 0 {
                        lean_ctor_set(v___x_1958_, 0, v___x_1982_);
                        v___x_1984_ = v___x_1958_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
                        v___x_1984_ = v_reuseFailAlloc_1985_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1969_ = l_Lean_Json_parseTagged___closed__0;
                v___x_1970_ = l_Nat_reprFast(v___x_1964_);
                v___x_1971_ = lean_string_append(v___x_1969_, v___x_1970_);
                lean_dec_ref(v___x_1970_);
                v___x_1972_ = l_Lean_Json_parseTagged___closed__1;
                v___x_1973_ = lean_string_append(v___x_1971_, v___x_1972_);
                v___x_1974_ = l_Nat_reprFast(v_nFields_1943_);
                v___x_1975_ = lean_string_append(v___x_1973_, v___x_1974_);
                lean_dec_ref(v___x_1974_);
                if v_isShared_1968_ == 0 {
                    lean_ctor_set_tag(v___x_1967_, 0);
                    lean_ctor_set(v___x_1967_, 0, v___x_1975_);
                    v___x_1977_ = v___x_1967_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1977_;
            }
            6 => {
                return v___x_1984_;
            }
            7 => {
                if v_isShared_1997_ == 0 {
                    v___x_1999_ = v___x_1996_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
                    v___x_1999_ = v_reuseFailAlloc_2000_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1999_;
            }
            9 => {
                v___x_2006_ = lean_string_dec_eq(v_a_2002_, v_tag_1942_);
                if v___x_2006_ == 0 {
                    v___x_2007_ = l_Lean_Json_parseTagged___closed__3;
                    v___x_2008_ = lean_string_append(v___x_2007_, v_a_2002_);
                    lean_dec(v_a_2002_);
                    v___x_2009_ = l_Lean_Json_parseTagged___closed__1;
                    v___x_2010_ = lean_string_append(v___x_2008_, v___x_2009_);
                    v___x_2011_ = lean_string_append(v___x_2010_, v_tag_1942_);
                    if v_isShared_2005_ == 0 {
                        lean_ctor_set_tag(v___x_2004_, 0);
                        lean_ctor_set(v___x_2004_, 0, v___x_2011_);
                        v___x_2013_ = v___x_2004_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2014_, 0, v___x_2011_);
                        v___x_2013_ = v_reuseFailAlloc_2014_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2004_);
                    lean_dec(v_a_2002_);
                    v___x_2015_ = l_Lean_Json_parseTagged___closed__4;
                    return v___x_2015_;
                }
            }
            10 => {
                return v___x_2013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_parseTagged___boxed(
    mut v_json_2017_: *mut LeanObject,
    mut v_tag_2018_: *mut LeanObject,
    mut v_nFields_2019_: *mut LeanObject,
    mut v_fieldNames_x3f_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2021_: *mut LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Lean_Json_parseTagged(
        v_json_2017_,
        v_tag_2018_,
        v_nFields_2019_,
        v_fieldNames_x3f_2020_,
    );
    lean_dec(v_fieldNames_x3f_2020_);
    lean_dec_ref(v_tag_2018_);
    return v_res_2021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(
    mut v_a_2022_: *mut LeanObject,
    mut v_sz_2023_: usize,
    mut v_i_2024_: usize,
    mut v_bs_2025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2026_: u8 = 0;
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2034_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: usize = 0;
    let mut v___x_2043_: usize = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2026_ = lean_usize_dec_lt(v_i_2024_, v_sz_2023_);
                if v___x_2026_ == 0 {
                    lean_dec(v_a_2022_);
                    v___x_2027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2027_, 0, v_bs_2025_);
                    return v___x_2027_;
                } else {
                    v_v_2028_ = lean_array_uget_borrowed(v_bs_2025_, v_i_2024_);
                    v___x_2029_ = l_Lean_Name_getString_x21(v_v_2028_);
                    lean_inc(v_a_2022_);
                    v___x_2030_ = l_Lean_Json_getObjVal_x3f(v_a_2022_, v___x_2029_);
                    lean_dec_ref(v___x_2029_);
                    if lean_obj_tag(v___x_2030_) == 0 {
                        lean_dec_ref(v_bs_2025_);
                        lean_dec(v_a_2022_);
                        v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
                        v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2030_)) as u8;
                        if v_isSharedCheck_2038_ == 0 {
                            v___x_2033_ = v___x_2030_;
                            v_isShared_2034_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2031_);
                            lean_dec(v___x_2030_);
                            v___x_2033_ = lean_box(0);
                            v_isShared_2034_ = v_isSharedCheck_2038_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2039_ = lean_ctor_get(v___x_2030_, 0);
                        lean_inc(v_a_2039_);
                        lean_dec_ref_known(v___x_2030_, 1);
                        v___x_2040_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2041_ = lean_array_uset(v_bs_2025_, v_i_2024_, v___x_2040_);
                        v___x_2042_ = 1usize;
                        v___x_2043_ = lean_usize_add(v_i_2024_, v___x_2042_);
                        v___x_2044_ = lean_array_uset(v_bs_x27_2041_, v_i_2024_, v_a_2039_);
                        v_i_2024_ = v___x_2043_;
                        v_bs_2025_ = v___x_2044_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2034_ == 0 {
                    v___x_2036_ = v___x_2033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2037_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2031_);
                    v___x_2036_ = v_reuseFailAlloc_2037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0___boxed(
    mut v_a_2046_: *mut LeanObject,
    mut v_sz_2047_: *mut LeanObject,
    mut v_i_2048_: *mut LeanObject,
    mut v_bs_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2050_: usize = 0;
    let mut v_i_boxed_2051_: usize = 0;
    let mut v_res_2052_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2050_ = lean_unbox_usize(v_sz_2047_);
    lean_dec(v_sz_2047_);
    v_i_boxed_2051_ = lean_unbox_usize(v_i_2048_);
    lean_dec(v_i_2048_);
    v_res_2052_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_2046_, v_sz_boxed_2050_, v_i_boxed_2051_, v_bs_2049_);
    return v_res_2052_;
}
pub unsafe fn l_Lean_Json_parseCtorFields(
    mut v_json_2053_: *mut LeanObject,
    mut v_tag_2054_: *mut LeanObject,
    mut v_nFields_2055_: *mut LeanObject,
    mut v_fieldNames_x3f_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2061_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2065_: u8 = 0;
    let mut v_a_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2069_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2078_: u8 = 0;
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2096_: u8 = 0;
    let mut v_a_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2099_: usize = 0;
    let mut v___x_2100_: usize = 0;
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2057_ = l_Lean_Json_getObjVal_x3f(v_json_2053_, v_tag_2054_);
                if lean_obj_tag(v___x_2057_) == 0 {
                    lean_dec(v_fieldNames_x3f_2056_);
                    lean_dec(v_nFields_2055_);
                    v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
                    v_isSharedCheck_2065_ = (!lean_is_exclusive(v___x_2057_)) as u8;
                    if v_isSharedCheck_2065_ == 0 {
                        v___x_2060_ = v___x_2057_;
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2058_);
                        lean_dec(v___x_2057_);
                        v___x_2060_ = lean_box(0);
                        v_isShared_2061_ = v_isSharedCheck_2065_;
                        state = 1;
                        continue;
                    }
                } else {
                    if lean_obj_tag(v_fieldNames_x3f_2056_) == 0 {
                        v_a_2066_ = lean_ctor_get(v___x_2057_, 0);
                        v_isSharedCheck_2096_ = (!lean_is_exclusive(v___x_2057_)) as u8;
                        if v_isSharedCheck_2096_ == 0 {
                            v___x_2068_ = v___x_2057_;
                            v_isShared_2069_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2066_);
                            lean_dec(v___x_2057_);
                            v___x_2068_ = lean_box(0);
                            v_isShared_2069_ = v_isSharedCheck_2096_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_nFields_2055_);
                        v_a_2097_ = lean_ctor_get(v___x_2057_, 0);
                        lean_inc(v_a_2097_);
                        lean_dec_ref_known(v___x_2057_, 1);
                        v_val_2098_ = lean_ctor_get(v_fieldNames_x3f_2056_, 0);
                        lean_inc(v_val_2098_);
                        lean_dec_ref_known(v_fieldNames_x3f_2056_, 1);
                        v_sz_2099_ = lean_array_size(v_val_2098_);
                        v___x_2100_ = 0usize;
                        v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Json_parseCtorFields_spec__0(v_a_2097_, v_sz_2099_, v___x_2100_, v_val_2098_);
                        return v___x_2101_;
                    }
                }
            }
            1 => {
                if v_isShared_2061_ == 0 {
                    v___x_2063_ = v___x_2060_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
                    v___x_2063_ = v_reuseFailAlloc_2064_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2063_;
            }
            3 => {
                v___x_2070_ = lean_unsigned_to_nat(1);
                v___x_2071_ = lean_nat_dec_eq(v_nFields_2055_, v___x_2070_);
                if v___x_2071_ == 0 {
                    lean_del_object(v___x_2068_);
                    v___x_2072_ = l_Lean_Json_getArr_x3f(v_a_2066_);
                    if lean_obj_tag(v___x_2072_) == 0 {
                        lean_dec(v_nFields_2055_);
                        return v___x_2072_;
                    } else {
                        v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
                        lean_inc(v_a_2073_);
                        v___x_2074_ = lean_array_get_size(v_a_2073_);
                        lean_dec(v_a_2073_);
                        v___x_2075_ = lean_nat_dec_eq(v___x_2074_, v_nFields_2055_);
                        if v___x_2075_ == 0 {
                            v_isSharedCheck_2089_ = (!lean_is_exclusive(v___x_2072_)) as u8;
                            if v_isSharedCheck_2089_ == 0 {
                                v_unused_2090_ = lean_ctor_get(v___x_2072_, 0);
                                lean_dec(v_unused_2090_);
                                v___x_2077_ = v___x_2072_;
                                v_isShared_2078_ = v_isSharedCheck_2089_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_2072_);
                                v___x_2077_ = lean_box(0);
                                v_isShared_2078_ = v_isSharedCheck_2089_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec(v_nFields_2055_);
                            return v___x_2072_;
                        }
                    }
                } else {
                    lean_dec(v_nFields_2055_);
                    v___x_2091_ = lean_mk_empty_array_with_capacity(v___x_2070_);
                    v___x_2092_ = lean_array_push(v___x_2091_, v_a_2066_);
                    if v_isShared_2069_ == 0 {
                        lean_ctor_set(v___x_2068_, 0, v___x_2092_);
                        v___x_2094_ = v___x_2068_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2095_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
                        v___x_2094_ = v_reuseFailAlloc_2095_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2079_ = l_Lean_Json_parseTagged___closed__0;
                v___x_2080_ = l_Nat_reprFast(v___x_2074_);
                v___x_2081_ = lean_string_append(v___x_2079_, v___x_2080_);
                lean_dec_ref(v___x_2080_);
                v___x_2082_ = l_Lean_Json_parseTagged___closed__1;
                v___x_2083_ = lean_string_append(v___x_2081_, v___x_2082_);
                v___x_2084_ = l_Nat_reprFast(v_nFields_2055_);
                v___x_2085_ = lean_string_append(v___x_2083_, v___x_2084_);
                lean_dec_ref(v___x_2084_);
                if v_isShared_2078_ == 0 {
                    lean_ctor_set_tag(v___x_2077_, 0);
                    lean_ctor_set(v___x_2077_, 0, v___x_2085_);
                    v___x_2087_ = v___x_2077_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2087_;
            }
            6 => {
                return v___x_2094_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_parseCtorFields___boxed(
    mut v_json_2102_: *mut LeanObject,
    mut v_tag_2103_: *mut LeanObject,
    mut v_nFields_2104_: *mut LeanObject,
    mut v_fieldNames_x3f_2105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2106_: *mut LeanObject = core::ptr::null_mut();
    v_res_2106_ = l_Lean_Json_parseCtorFields(
        v_json_2102_,
        v_tag_2103_,
        v_nFields_2104_,
        v_fieldNames_x3f_2105_,
    );
    lean_dec_ref(v_tag_2103_);
    return v_res_2106_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_GetLit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_FromToJson_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_GetLit(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_FromToJson_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Json_FromToJson_Basic(builtin);
}
