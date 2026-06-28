// Lean compiler output
// Module: Lean.Data.Json.Basic
// Imports: Init.Data.Range Init.Data.OfScientific Init.Data.Hashable Std.Data.TreeMap.Raw.Basic Init.Data.Ord.String Init.Data.Range.Polymorphic.Iterators Init.Data.Range.Polymorphic.Nat Init.Data.String.Substring Init.Data.ToString.Macro
use crate::r#gen::Init::Data::Hashable::{
    initialize_Init_Data_Hashable, runtime_initialize_Init_Data_Hashable,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::OfScientific::{
    initialize_Init_Data_OfScientific, l_Float_ofScientific, lean_float_of_nat,
    runtime_initialize_Init_Data_OfScientific,
};
use crate::r#gen::Init::Data::Ord::String::{
    initialize_Init_Data_Ord_String, runtime_initialize_Init_Data_Ord_String,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Nat::{
    initialize_Init_Data_Range_Polymorphic_Nat, runtime_initialize_Init_Data_Range_Polymorphic_Nat,
};
use crate::r#gen::Init::Data::Range::{
    initialize_Init_Data_Range, runtime_initialize_Init_Data_Range,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::Data::String::Substring::{
    initialize_Init_Data_String_Substring, l_Substring_Raw_nextn,
    runtime_initialize_Init_Data_String_Substring,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_decodeScientificLitVal_x3f;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Std::Data::TreeMap::Raw::Basic::{
    initialize_Std_Data_TreeMap_Raw_Basic, runtime_initialize_Std_Data_TreeMap_Raw_Basic,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::Float::{
    lean_float_beq, lean_float_decLt, lean_float_isinf, lean_float_isnan, lean_float_mul,
    lean_float_negate, lean_float_to_string,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Ord::String::lean_string_compare;
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_dec_lt, lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_prev,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul, lean_nat_pow,
    lean_nat_sub, lean_panic_fn_borrowed, lean_string_dec_eq, lean_string_hash,
    lean_string_utf8_byte_size, lean_uint32_dec_eq, lean_uint64_mix_hash, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_box, lean_box_float,
    lean_box_uint64, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_float, lean_unbox_uint64, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l_Lean_instHashableJsonNumber_hash___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instHashableJsonNumber_hash___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instHashableJsonNumber___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableJsonNumber_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableJsonNumber___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableJsonNumber___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instHashableJsonNumber: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableJsonNumber___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instCoeNat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_fromNat as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instCoeNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instCoeNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instCoeInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_fromInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instCoeInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instCoeInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeInt___closed__0_value) as *mut LeanObject;
static mut l_Lean_JsonNumber_normalize___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_normalize___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_normalize___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_normalize___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_normalize___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_JsonNumber_ltProp: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_JsonNumber_instOrd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_JsonNumber_instOrd___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_JsonNumber_instOrd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOrd___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instOrd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOrd___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_toString___closed__0_value: LeanStringObject<2> = LeanStringObject {
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
static mut l_Lean_JsonNumber_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_toString___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [101, 0],
};
static mut l_Lean_JsonNumber_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__1_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_toString___closed__2_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_JsonNumber_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__2_value) as *mut LeanObject;
static mut l_Lean_JsonNumber_toString___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_toString___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_JsonNumber_toString___closed__4_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [45, 0],
};
static mut l_Lean_JsonNumber_toString___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__4_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 168, 0],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__1_value: LeanStringObject<2> =
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
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__3_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 1,
        m_data: [226, 159, 169, 0],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__6_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__7_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__3_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__7_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instRepr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_JsonNumber_instRepr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_JsonNumber_instRepr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instRepr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instOfScientific___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_instOfScientific___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instOfScientific___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOfScientific___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instOfScientific: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOfScientific___closed__0_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_JsonNumber_instNeg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_JsonNumber_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_JsonNumber_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instNeg___closed__0_value) as *mut LeanObject;
static mut l_Lean_JsonNumber_instInhabited___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_instInhabited___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_JsonNumber_instInhabited: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_toFloat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_toFloat___closed__0: f64 = 0.0;
static mut l_Lean_JsonNumber_toFloat___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_toFloat___closed__1: f64 = 0.0;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 74, 115, 111, 110, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value: LeanStringObject<67> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 74, 115, 111, 110, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110, 46, 74, 115, 111, 110, 78, 117, 109, 98, 101, 114, 46, 102, 114, 111, 109, 80, 111, 115, 105, 116, 105, 118, 101, 70, 108, 111, 97, 116, 33, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value
) as *mut LeanObject;
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__0: f64 = 0.0;
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__2: f64 = 0.0;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__3_value: LeanStringObject<10> =
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
        m_data: [45, 73, 110, 102, 105, 110, 105, 116, 121, 0],
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__3_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__4_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__5_value: LeanStringObject<9> =
    LeanStringObject {
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
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__5_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__6_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__7_value: LeanStringObject<4> =
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
        m_data: [78, 97, 78, 0],
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__7_value) as *mut LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__8_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__7_value) as *mut LeanObject,
    ],
};
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__8_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedJson_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedJson: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instBEq___private__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instBEq___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0: u64 = 0;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1: u64 = 0;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2: u64 = 0;
pub static l_Lean_Json_instHashable___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instHashable___private__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instHashable___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instHashable___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instHashable: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instHashable___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instCoeNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instCoeNat___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeNat___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instCoeNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instCoeInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instCoeInt___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instCoeInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeInt___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instCoeString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instCoeString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeString___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instCoeString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeString___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instCoeBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Json_instCoeBool___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeBool___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instCoeBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObj_x3f___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        111, 98, 106, 101, 99, 116, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getObj_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObj_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getObj_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getArr_x3f___closed__0_value: LeanStringObject<15> = LeanStringObject {
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
        97, 114, 114, 97, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getArr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getArr_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getArr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getStr_x3f___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        83, 116, 114, 105, 110, 103, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getStr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getStr_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getStr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getNat_x3f___closed__0_value: LeanStringObject<24> = LeanStringObject {
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
        78, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 32, 101, 120, 112, 101,
        99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getNat_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getNat_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getNat_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getInt_x3f___closed__0_value: LeanStringObject<17> = LeanStringObject {
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
        73, 110, 116, 101, 103, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getInt_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getInt_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getInt_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getBool_x3f___closed__0_value: LeanStringObject<14> = LeanStringObject {
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
        66, 111, 111, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getBool_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getBool_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getBool_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getNum_x3f___closed__0_value: LeanStringObject<16> = LeanStringObject {
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
        110, 117, 109, 98, 101, 114, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Json_getNum_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getNum_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getNum_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getObjVal_x3f___closed__0_value: LeanStringObject<21> = LeanStringObject {
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
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 0,
    ],
};
static mut l_Lean_Json_getObjVal_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObjVal_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getObjVal_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getObjVal_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObjVal_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Json_getArrVal_x3f___closed__0_value: LeanStringObject<22> = LeanStringObject {
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
        105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115,
        58, 32, 0,
    ],
};
static mut l_Lean_Json_getArrVal_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArrVal_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_getArrVal_x3f___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value) as *mut LeanObject],
};
static mut l_Lean_Json_getArrVal_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArrVal_x3f___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value) as *mut LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_setObjVal_x21___closed__0_value: LeanStringObject<21> = LeanStringObject {
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
        76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 115, 101, 116, 79, 98, 106, 86, 97, 108, 33, 0,
    ],
};
static mut l_Lean_Json_setObjVal_x21___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_setObjVal_x21___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_setObjVal_x21___closed__1_value: LeanStringObject<36> = LeanStringObject {
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
        74, 115, 111, 110, 46, 115, 101, 116, 79, 98, 106, 86, 97, 108, 33, 58, 32, 110, 111, 116,
        32, 97, 110, 32, 111, 98, 106, 101, 99, 116, 58, 32, 123, 106, 125, 0,
    ],
};
static mut l_Lean_Json_setObjVal_x21___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_setObjVal_x21___closed__1_value) as *mut LeanObject;
static mut l_Lean_Json_setObjVal_x21___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Json_setObjVal_x21___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_instCoeArrayStructured___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeArrayStructured___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeArrayStructured___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeArrayStructured___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Json_instCoeArrayStructured: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeArrayStructured___closed__0_value) as *mut LeanObject;
pub static l_Lean_Json_instCoeRawStringStructured___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeRawStringStructured___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeRawStringStructured___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeRawStringStructured___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Json_instCoeRawStringStructured: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeRawStringStructured___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_instDecidableEqJsonNumber_decEq(
    mut v_x_1897_: *mut LeanObject,
    mut v_x_1898_: *mut LeanObject,
) -> u8 {
    let mut v_mantissa_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    v_mantissa_1899_ = lean_ctor_get(v_x_1897_, 0);
    v_exponent_1900_ = lean_ctor_get(v_x_1897_, 1);
    v_mantissa_1901_ = lean_ctor_get(v_x_1898_, 0);
    v_exponent_1902_ = lean_ctor_get(v_x_1898_, 1);
    v___x_1903_ = lean_int_dec_eq(v_mantissa_1899_, v_mantissa_1901_);
    if v___x_1903_ == 0 {
        return v___x_1903_;
    } else {
        let mut v___x_1904_: u8 = 0;
        v___x_1904_ = lean_nat_dec_eq(v_exponent_1900_, v_exponent_1902_);
        return v___x_1904_;
    }
}
pub unsafe fn l_Lean_instDecidableEqJsonNumber_decEq___boxed(
    mut v_x_1905_: *mut LeanObject,
    mut v_x_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1907_: u8 = 0;
    let mut v_r_1908_: *mut LeanObject = core::ptr::null_mut();
    v_res_1907_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_1905_, v_x_1906_);
    lean_dec_ref(v_x_1906_);
    lean_dec_ref(v_x_1905_);
    v_r_1908_ = lean_box((v_res_1907_) as usize);
    return v_r_1908_;
}
pub unsafe fn l_Lean_instDecidableEqJsonNumber(
    mut v_x_1909_: *mut LeanObject,
    mut v_x_1910_: *mut LeanObject,
) -> u8 {
    let mut v___x_1911_: u8 = 0;
    v___x_1911_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_1909_, v_x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_instDecidableEqJsonNumber___boxed(
    mut v_x_1912_: *mut LeanObject,
    mut v_x_1913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1914_: u8 = 0;
    let mut v_r_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_instDecidableEqJsonNumber(v_x_1912_, v_x_1913_);
    lean_dec_ref(v_x_1913_);
    lean_dec_ref(v_x_1912_);
    v_r_1915_ = lean_box((v_res_1914_) as usize);
    return v_r_1915_;
}
pub unsafe fn _init_l_Lean_instHashableJsonNumber_hash___closed__0() -> *mut LeanObject {
    let mut v_natZero_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1917_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_1916_ = lean_unsigned_to_nat(0);
    v_intZero_1917_ = lean_nat_to_int(v_natZero_1916_);
    return v_intZero_1917_;
}
pub unsafe fn l_Lean_instHashableJsonNumber_hash(mut v_x_1918_: *mut LeanObject) -> u64 {
    let mut v_mantissa_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u64 = 0;
    let mut v___y_1923_: u64 = 0;
    let mut v___x_1924_: u64 = 0;
    let mut v___x_1925_: u64 = 0;
    let mut v___x_1926_: u64 = 0;
    let mut v_intZero_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1928_: u8 = 0;
    let mut v_a_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u64 = 0;
    let mut v_abs_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1919_ = lean_ctor_get(v_x_1918_, 0);
                v_exponent_1920_ = lean_ctor_get(v_x_1918_, 1);
                v___x_1921_ = 0u64;
                v_intZero_1927_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v_isNeg_1928_ = lean_int_dec_lt(v_mantissa_1919_, v_intZero_1927_);
                if v_isNeg_1928_ == 0 {
                    v_a_1929_ = lean_nat_abs(v_mantissa_1919_);
                    v___x_1930_ = lean_unsigned_to_nat(2);
                    v___x_1931_ = lean_nat_mul(v___x_1930_, v_a_1929_);
                    lean_dec(v_a_1929_);
                    v___x_1932_ = lean_uint64_of_nat(v___x_1931_);
                    lean_dec(v___x_1931_);
                    v___y_1923_ = v___x_1932_;
                    state = 1;
                    continue;
                } else {
                    v_abs_1933_ = lean_nat_abs(v_mantissa_1919_);
                    v_one_1934_ = lean_unsigned_to_nat(1);
                    v_a_1935_ = lean_nat_sub(v_abs_1933_, v_one_1934_);
                    lean_dec(v_abs_1933_);
                    v___x_1936_ = lean_unsigned_to_nat(2);
                    v___x_1937_ = lean_nat_mul(v___x_1936_, v_a_1935_);
                    lean_dec(v_a_1935_);
                    v___x_1938_ = lean_nat_add(v___x_1937_, v_one_1934_);
                    lean_dec(v___x_1937_);
                    v___x_1939_ = lean_uint64_of_nat(v___x_1938_);
                    lean_dec(v___x_1938_);
                    v___y_1923_ = v___x_1939_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1924_ = lean_uint64_mix_hash(v___x_1921_, v___y_1923_);
                v___x_1925_ = lean_uint64_of_nat(v_exponent_1920_);
                v___x_1926_ = lean_uint64_mix_hash(v___x_1924_, v___x_1925_);
                return v___x_1926_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instHashableJsonNumber_hash___boxed(
    mut v_x_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1941_: u64 = 0;
    let mut v_r_1942_: *mut LeanObject = core::ptr::null_mut();
    v_res_1941_ = l_Lean_instHashableJsonNumber_hash(v_x_1940_);
    lean_dec_ref(v_x_1940_);
    v_r_1942_ = lean_box_uint64(v_res_1941_);
    return v_r_1942_;
}
pub unsafe fn l_Nat_cast___at___00Lean_JsonNumber_fromNat_spec__0(
    mut v_a_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    v___x_1946_ = lean_nat_to_int(v_a_1945_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_JsonNumber_fromNat(mut v_n_1947_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_nat_to_int(v_n_1947_);
    v___x_1949_ = lean_unsigned_to_nat(0);
    v___x_1950_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1950_, 0, v___x_1948_);
    lean_ctor_set(v___x_1950_, 1, v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_JsonNumber_fromInt(mut v_n_1951_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    v___x_1952_ = lean_unsigned_to_nat(0);
    v___x_1953_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1953_, 0, v_n_1951_);
    lean_ctor_set(v___x_1953_, 1, v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_JsonNumber_instOfNat(mut v_n_1958_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    v___x_1959_ = l_Lean_JsonNumber_fromNat(v_n_1958_);
    return v___x_1959_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(
    mut v_n_1960_: *mut LeanObject,
    mut v_digits_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_unsigned_to_nat(9);
                v___x_1963_ = lean_nat_dec_le(v_n_1960_, v___x_1962_);
                if v___x_1963_ == 0 {
                    v___x_1964_ = lean_unsigned_to_nat(10);
                    v___x_1965_ = lean_nat_div(v_n_1960_, v___x_1964_);
                    lean_dec(v_n_1960_);
                    v___x_1966_ = lean_unsigned_to_nat(1);
                    v___x_1967_ = lean_nat_add(v_digits_1961_, v___x_1966_);
                    lean_dec(v_digits_1961_);
                    v_n_1960_ = v___x_1965_;
                    v_digits_1961_ = v___x_1967_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_n_1960_);
                    return v_digits_1961_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(
    mut v_n_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = lean_unsigned_to_nat(1);
    v___x_1971_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(
        v_n_1969_,
        v___x_1970_,
    );
    return v___x_1971_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
    mut v_upperBound_1972_: *mut LeanObject,
    mut v_a_1973_: *mut LeanObject,
    mut v_b_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1975_ = lean_nat_dec_lt(v_a_1973_, v_upperBound_1972_);
                if v___x_1975_ == 0 {
                    lean_dec(v_a_1973_);
                    return v_b_1974_;
                } else {
                    v___x_1976_ = lean_unsigned_to_nat(0);
                    v___x_1977_ = lean_unsigned_to_nat(10);
                    v___x_1978_ = lean_nat_mod(v_b_1974_, v___x_1977_);
                    v___x_1979_ = lean_nat_dec_eq(v___x_1978_, v___x_1976_);
                    lean_dec(v___x_1978_);
                    if v___x_1979_ == 0 {
                        lean_dec(v_a_1973_);
                        return v_b_1974_;
                    } else {
                        v___x_1980_ = lean_nat_div(v_b_1974_, v___x_1977_);
                        lean_dec(v_b_1974_);
                        v___x_1981_ = lean_unsigned_to_nat(1);
                        v___x_1982_ = lean_nat_add(v_a_1973_, v___x_1981_);
                        lean_dec(v_a_1973_);
                        v_a_1973_ = v___x_1982_;
                        v_b_1974_ = v___x_1980_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg___boxed(
    mut v_upperBound_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_b_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1987_: *mut LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
        v_upperBound_1984_,
        v_a_1985_,
        v_b_1986_,
    );
    lean_dec(v_upperBound_1984_);
    return v_res_1987_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__0() -> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = lean_unsigned_to_nat(1);
    v___x_1989_ = lean_nat_to_int(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__1() -> *mut LeanObject {
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    v___x_1990_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
        _init_l_Lean_JsonNumber_normalize___closed__0,
    );
    v___x_1991_ = lean_int_neg(v___x_1990_);
    return v___x_1991_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__2() -> *mut LeanObject {
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    v___x_1992_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
        _init_l_Lean_instHashableJsonNumber_hash___closed__0,
    );
    v___x_1993_ = lean_unsigned_to_nat(0);
    v___x_1994_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1994_, 0, v___x_1993_);
    lean_ctor_set(v___x_1994_, 1, v___x_1992_);
    return v___x_1994_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__3() -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__2_once),
        _init_l_Lean_JsonNumber_normalize___closed__2,
    );
    v___x_1996_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
        _init_l_Lean_instHashableJsonNumber_hash___closed__0,
    );
    v___x_1997_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1997_, 0, v___x_1996_);
    lean_ctor_set(v___x_1997_, 1, v___x_1995_);
    return v___x_1997_;
}
pub unsafe fn l_Lean_JsonNumber_normalize(mut v_x_1998_: *mut LeanObject) -> *mut LeanObject {
    let mut v_mantissa_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mAbs_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nDigits_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1999_ = lean_ctor_get(v_x_1998_, 0);
                v_exponent_2000_ = lean_ctor_get(v_x_1998_, 1);
                v_isSharedCheck_2024_ = (!lean_is_exclusive(v_x_1998_)) as u8;
                if v_isSharedCheck_2024_ == 0 {
                    v___x_2002_ = v_x_1998_;
                    v_isShared_2003_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exponent_2000_);
                    lean_inc(v_mantissa_1999_);
                    lean_dec(v_x_1998_);
                    v___x_2002_ = lean_box(0);
                    v_isShared_2003_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2004_ = lean_unsigned_to_nat(0);
                v___x_2018_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2019_ = lean_int_dec_eq(v_mantissa_1999_, v___x_2018_);
                if v___x_2019_ == 0 {
                    v___x_2020_ = lean_int_dec_lt(v___x_2018_, v_mantissa_1999_);
                    if v___x_2020_ == 0 {
                        v___x_2021_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1_once),
                            _init_l_Lean_JsonNumber_normalize___closed__1,
                        );
                        v___y_2006_ = v___x_2021_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2022_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
                            _init_l_Lean_JsonNumber_normalize___closed__0,
                        );
                        v___y_2006_ = v___x_2022_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2002_);
                    lean_dec(v_exponent_2000_);
                    lean_dec(v_mantissa_1999_);
                    v___x_2023_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__3_once),
                        _init_l_Lean_JsonNumber_normalize___closed__3,
                    );
                    return v___x_2023_;
                }
            }
            2 => {
                v_mAbs_2007_ = lean_nat_abs(v_mantissa_1999_);
                lean_dec(v_mantissa_1999_);
                lean_inc(v_mAbs_2007_);
                v_nDigits_2008_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_mAbs_2007_);
                v___x_2009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_nDigits_2008_, v___x_2004_, v_mAbs_2007_);
                v___x_2010_ = lean_nat_to_int(v_exponent_2000_);
                v___x_2011_ = lean_int_neg(v___x_2010_);
                lean_dec(v___x_2010_);
                v___x_2012_ = lean_nat_to_int(v_nDigits_2008_);
                v___x_2013_ = lean_int_add(v___x_2011_, v___x_2012_);
                lean_dec(v___x_2012_);
                lean_dec(v___x_2011_);
                if v_isShared_2003_ == 0 {
                    lean_ctor_set(v___x_2002_, 1, v___x_2013_);
                    lean_ctor_set(v___x_2002_, 0, v___x_2009_);
                    v___x_2015_ = v___x_2002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2009_);
                    lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2013_);
                    v___x_2015_ = v_reuseFailAlloc_2017_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v___y_2006_);
                v___x_2016_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2016_, 0, v___y_2006_);
                lean_ctor_set(v___x_2016_, 1, v___x_2015_);
                return v___x_2016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(
    mut v_upperBound_2025_: *mut LeanObject,
    mut v_inst_2026_: *mut LeanObject,
    mut v_R_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_b_2029_: *mut LeanObject,
    mut v_c_2030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
        v_upperBound_2025_,
        v_a_2028_,
        v_b_2029_,
    );
    return v___x_2031_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___boxed(
    mut v_upperBound_2032_: *mut LeanObject,
    mut v_inst_2033_: *mut LeanObject,
    mut v_R_2034_: *mut LeanObject,
    mut v_a_2035_: *mut LeanObject,
    mut v_b_2036_: *mut LeanObject,
    mut v_c_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2038_: *mut LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(
        v_upperBound_2032_,
        v_inst_2033_,
        v_R_2034_,
        v_a_2035_,
        v_b_2036_,
        v_c_2037_,
    );
    lean_dec(v_upperBound_2032_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_JsonNumber_lt(
    mut v_a_2039_: *mut LeanObject,
    mut v_b_2040_: *mut LeanObject,
) -> u8 {
    let mut v___y_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: u8 = 0;
    let mut v___y_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: u8 = 0;
    let mut v_fst_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_amDigits_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bmDigits_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = l_Lean_JsonNumber_normalize(v_a_2039_);
                v_fst_2069_ = lean_ctor_get(v___x_2068_, 0);
                lean_inc(v_fst_2069_);
                v_snd_2070_ = lean_ctor_get(v___x_2068_, 1);
                lean_inc(v_snd_2070_);
                lean_dec_ref(v___x_2068_);
                v___x_2071_ = l_Lean_JsonNumber_normalize(v_b_2040_);
                v_fst_2072_ = lean_ctor_get(v___x_2071_, 0);
                lean_inc(v_fst_2072_);
                v_snd_2073_ = lean_ctor_get(v___x_2071_, 1);
                lean_inc(v_snd_2073_);
                lean_dec_ref(v___x_2071_);
                v___x_2080_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
                    _init_l_Lean_JsonNumber_normalize___closed__0,
                );
                v___x_2081_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1_once),
                    _init_l_Lean_JsonNumber_normalize___closed__1,
                );
                v___x_2082_ = lean_int_dec_eq(v_fst_2069_, v___x_2081_);
                if v___x_2082_ == 0 {
                    v___x_2083_ = lean_int_dec_eq(v_fst_2069_, v___x_2080_);
                    if v___x_2083_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_2084_ = lean_int_dec_eq(v_fst_2072_, v___x_2081_);
                        if v___x_2084_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v_snd_2073_);
                            lean_dec(v_fst_2072_);
                            lean_dec(v_snd_2070_);
                            lean_dec(v_fst_2069_);
                            return v___x_2082_;
                        }
                    }
                } else {
                    v___x_2085_ = lean_int_dec_eq(v_fst_2072_, v___x_2080_);
                    if v___x_2085_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_snd_2073_);
                        lean_dec(v_fst_2072_);
                        lean_dec(v_snd_2070_);
                        lean_dec(v_fst_2069_);
                        return v___x_2085_;
                    }
                }
            }
            1 => {
                if v___y_2043_ == 0 {
                    v___x_2047_ = lean_int_dec_lt(v___y_2042_, v___y_2044_);
                    lean_dec(v___y_2044_);
                    lean_dec(v___y_2042_);
                    if v___x_2047_ == 0 {
                        v___x_2048_ = lean_nat_dec_lt(v_fst_2045_, v_snd_2046_);
                        lean_dec(v_snd_2046_);
                        lean_dec(v_fst_2045_);
                        return v___x_2048_;
                    } else {
                        lean_dec(v_snd_2046_);
                        lean_dec(v_fst_2045_);
                        return v___y_2043_;
                    }
                } else {
                    lean_dec(v_snd_2046_);
                    lean_dec(v_fst_2045_);
                    lean_dec(v___y_2044_);
                    lean_dec(v___y_2042_);
                    return v___y_2043_;
                }
            }
            2 => {
                v_fst_2052_ = lean_ctor_get(v_fst_2050_, 0);
                lean_inc_n(v_fst_2052_, 2);
                v_snd_2053_ = lean_ctor_get(v_fst_2050_, 1);
                lean_inc(v_snd_2053_);
                lean_dec_ref(v_fst_2050_);
                v_fst_2054_ = lean_ctor_get(v_snd_2051_, 0);
                lean_inc_n(v_fst_2054_, 2);
                v_snd_2055_ = lean_ctor_get(v_snd_2051_, 1);
                lean_inc(v_snd_2055_);
                lean_dec_ref(v_snd_2051_);
                v_amDigits_2056_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_2052_);
                v_bmDigits_2057_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_2054_);
                v___x_2058_ = lean_int_dec_lt(v_snd_2053_, v_snd_2055_);
                v___x_2059_ = lean_nat_dec_lt(v_amDigits_2056_, v_bmDigits_2057_);
                if v___x_2059_ == 0 {
                    v___x_2060_ = lean_unsigned_to_nat(10);
                    v___x_2061_ = lean_nat_sub(v_amDigits_2056_, v_bmDigits_2057_);
                    lean_dec(v_bmDigits_2057_);
                    lean_dec(v_amDigits_2056_);
                    v___x_2062_ = lean_nat_pow(v___x_2060_, v___x_2061_);
                    lean_dec(v___x_2061_);
                    v___x_2063_ = lean_nat_mul(v_fst_2054_, v___x_2062_);
                    lean_dec(v___x_2062_);
                    lean_dec(v_fst_2054_);
                    v___y_2042_ = v_snd_2055_;
                    v___y_2043_ = v___x_2058_;
                    v___y_2044_ = v_snd_2053_;
                    v_fst_2045_ = v_fst_2052_;
                    v_snd_2046_ = v___x_2063_;
                    state = 1;
                    continue;
                } else {
                    v___x_2064_ = lean_unsigned_to_nat(10);
                    v___x_2065_ = lean_nat_sub(v_bmDigits_2057_, v_amDigits_2056_);
                    lean_dec(v_amDigits_2056_);
                    lean_dec(v_bmDigits_2057_);
                    v___x_2066_ = lean_nat_pow(v___x_2064_, v___x_2065_);
                    lean_dec(v___x_2065_);
                    v___x_2067_ = lean_nat_mul(v_fst_2052_, v___x_2066_);
                    lean_dec(v___x_2066_);
                    lean_dec(v_fst_2052_);
                    v___y_2042_ = v_snd_2055_;
                    v___y_2043_ = v___x_2058_;
                    v___y_2044_ = v_snd_2053_;
                    v_fst_2045_ = v___x_2067_;
                    v_snd_2046_ = v_fst_2054_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2075_ == 0 {
                    v_fst_2050_ = v_snd_2070_;
                    v_snd_2051_ = v_snd_2073_;
                    state = 2;
                    continue;
                } else {
                    v_fst_2050_ = v_snd_2073_;
                    v_snd_2051_ = v_snd_2070_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2077_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1_once),
                    _init_l_Lean_JsonNumber_normalize___closed__1,
                );
                v___x_2078_ = lean_int_dec_eq(v_fst_2069_, v___x_2077_);
                lean_dec(v_fst_2069_);
                if v___x_2078_ == 0 {
                    lean_dec(v_fst_2072_);
                    v___y_2075_ = v___x_2078_;
                    state = 3;
                    continue;
                } else {
                    v___x_2079_ = lean_int_dec_eq(v_fst_2072_, v___x_2077_);
                    lean_dec(v_fst_2072_);
                    v___y_2075_ = v___x_2079_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_lt___boxed(
    mut v_a_2086_: *mut LeanObject,
    mut v_b_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2088_: u8 = 0;
    let mut v_r_2089_: *mut LeanObject = core::ptr::null_mut();
    v_res_2088_ = l_Lean_JsonNumber_lt(v_a_2086_, v_b_2087_);
    v_r_2089_ = lean_box((v_res_2088_) as usize);
    return v_r_2089_;
}
pub unsafe fn _init_l_Lean_JsonNumber_ltProp() -> *mut LeanObject {
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___x_2090_ = lean_box(0);
    return v___x_2090_;
}
pub unsafe fn l_Lean_JsonNumber_instDecidableLt(
    mut v_a_2091_: *mut LeanObject,
    mut v_b_2092_: *mut LeanObject,
) -> u8 {
    let mut v___x_2093_: u8 = 0;
    v___x_2093_ = l_Lean_JsonNumber_lt(v_a_2091_, v_b_2092_);
    return v___x_2093_;
}
pub unsafe fn l_Lean_JsonNumber_instDecidableLt___boxed(
    mut v_a_2094_: *mut LeanObject,
    mut v_b_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2096_: u8 = 0;
    let mut v_r_2097_: *mut LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Lean_JsonNumber_instDecidableLt(v_a_2094_, v_b_2095_);
    v_r_2097_ = lean_box((v_res_2096_) as usize);
    return v_r_2097_;
}
pub unsafe fn l_Lean_JsonNumber_instOrd___lam__0(
    mut v_x_2098_: *mut LeanObject,
    mut v_y_2099_: *mut LeanObject,
) -> u8 {
    let mut v___x_2100_: u8 = 0;
    lean_inc_ref(v_y_2099_);
    lean_inc_ref(v_x_2098_);
    v___x_2100_ = l_Lean_JsonNumber_lt(v_x_2098_, v_y_2099_);
    if v___x_2100_ == 0 {
        let mut v___x_2101_: u8 = 0;
        v___x_2101_ = l_Lean_JsonNumber_lt(v_y_2099_, v_x_2098_);
        if v___x_2101_ == 0 {
            let mut v___x_2102_: u8 = 0;
            v___x_2102_ = 1;
            return v___x_2102_;
        } else {
            let mut v___x_2103_: u8 = 0;
            v___x_2103_ = 2;
            return v___x_2103_;
        }
    } else {
        let mut v___x_2104_: u8 = 0;
        lean_dec_ref(v_y_2099_);
        lean_dec_ref(v_x_2098_);
        v___x_2104_ = 0;
        return v___x_2104_;
    }
}
pub unsafe fn l_Lean_JsonNumber_instOrd___lam__0___boxed(
    mut v_x_2105_: *mut LeanObject,
    mut v_y_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2107_: u8 = 0;
    let mut v_r_2108_: *mut LeanObject = core::ptr::null_mut();
    v_res_2107_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_2105_, v_y_2106_);
    v_r_2108_ = lean_box((v_res_2107_) as usize);
    return v_r_2108_;
}
pub unsafe fn l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
    mut v_s_2111_: *mut LeanObject,
    mut v_begPos_2112_: *mut LeanObject,
    mut v_i_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2114_: u8 = 0;
    let mut v_i_x27_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_2116_: u32 = 0;
    let mut v___x_2117_: u32 = 0;
    let mut v___x_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2114_ = lean_nat_dec_lt(v_begPos_2112_, v_i_2113_);
                if v___x_2114_ == 0 {
                    return v_i_2113_;
                } else {
                    v_i_x27_2115_ = lean_string_utf8_prev(v_s_2111_, v_i_2113_);
                    v_c_2116_ = lean_string_utf8_get(v_s_2111_, v_i_x27_2115_);
                    v___x_2117_ = 48;
                    v___x_2118_ = lean_uint32_dec_eq(v_c_2116_, v___x_2117_);
                    if v___x_2118_ == 0 {
                        lean_dec(v_i_x27_2115_);
                        return v_i_2113_;
                    } else {
                        lean_dec(v_i_2113_);
                        v_i_2113_ = v_i_x27_2115_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0___boxed(
    mut v_s_2120_: *mut LeanObject,
    mut v_begPos_2121_: *mut LeanObject,
    mut v_i_2122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2123_: *mut LeanObject = core::ptr::null_mut();
    v_res_2123_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
        v_s_2120_,
        v_begPos_2121_,
        v_i_2122_,
    );
    lean_dec(v_begPos_2121_);
    lean_dec_ref(v_s_2120_);
    return v_res_2123_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toString___closed__3() -> *mut LeanObject {
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2127_ = lean_unsigned_to_nat(9);
    v___x_2128_ = lean_nat_to_int(v___x_2127_);
    return v___x_2128_;
}
pub unsafe fn l_Lean_JsonNumber_toString(mut v_x_2130_: *mut LeanObject) -> *mut LeanObject {
    let mut v___y_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: u8 = 0;
    let mut v___y_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: u8 = 0;
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_right_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_left_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___y_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exp_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2141_ = lean_ctor_get(v_x_2130_, 0);
                lean_inc(v_mantissa_2141_);
                v_exponent_2142_ = lean_ctor_get(v_x_2130_, 1);
                lean_inc(v_exponent_2142_);
                lean_dec_ref(v_x_2130_);
                v___x_2143_ = lean_unsigned_to_nat(0);
                v___x_2165_ = lean_nat_dec_eq(v_exponent_2142_, v___x_2143_);
                if v___x_2165_ == 0 {
                    v___x_2166_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_instHashableJsonNumber_hash___closed__0_once
                        ),
                        _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                    );
                    v___x_2190_ = lean_int_dec_le(v___x_2166_, v_mantissa_2141_);
                    if v___x_2190_ == 0 {
                        v___x_2191_ = l_Lean_JsonNumber_toString___closed__4;
                        v___y_2181_ = v___x_2191_;
                        state = 4;
                        continue;
                    } else {
                        v___x_2192_ = l_Lean_JsonNumber_toString___closed__2;
                        v___y_2181_ = v___x_2192_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_exponent_2142_);
                    v___x_2193_ = l_Int_repr(v_mantissa_2141_);
                    lean_dec(v_mantissa_2141_);
                    return v___x_2193_;
                }
            }
            1 => {
                lean_inc_ref(v___y_2132_);
                v___x_2136_ = lean_string_append(v___y_2132_, v___y_2133_);
                lean_dec_ref(v___y_2133_);
                v___x_2137_ = l_Lean_JsonNumber_toString___closed__0;
                v___x_2138_ = lean_string_append(v___x_2136_, v___x_2137_);
                v___x_2139_ = lean_string_append(v___x_2138_, v___y_2134_);
                lean_dec_ref(v___y_2134_);
                v___x_2140_ = lean_string_append(v___x_2139_, v___y_2135_);
                lean_dec_ref(v___y_2135_);
                return v___x_2140_;
            }
            2 => {
                if v___y_2151_ == 0 {
                    v___x_2152_ = lean_nat_add(v___y_2148_, v___y_2150_);
                    lean_dec(v___y_2150_);
                    lean_dec(v___y_2148_);
                    v___x_2153_ = l_Nat_reprFast(v___x_2152_);
                    v___x_2154_ = lean_string_utf8_byte_size(v___x_2153_);
                    lean_inc_ref(v___x_2153_);
                    v___x_2155_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2155_, 0, v___x_2153_);
                    lean_ctor_set(v___x_2155_, 1, v___x_2143_);
                    lean_ctor_set(v___x_2155_, 2, v___x_2154_);
                    v___x_2156_ = lean_unsigned_to_nat(1);
                    v___x_2157_ = l_Substring_Raw_nextn(v___x_2155_, v___x_2156_, v___x_2143_);
                    lean_dec_ref_known(v___x_2155_, 3);
                    v_e_2158_ =
                        l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
                            v___x_2153_,
                            v___x_2157_,
                            v___x_2154_,
                        );
                    v_right_2159_ = lean_string_utf8_extract(v___x_2153_, v___x_2157_, v_e_2158_);
                    lean_dec(v_e_2158_);
                    lean_dec(v___x_2157_);
                    lean_dec_ref(v___x_2153_);
                    if v___y_2145_ == 0 {
                        v___x_2160_ = l_Lean_JsonNumber_toString___closed__1;
                        v___x_2161_ = l_Int_repr(v___y_2149_);
                        lean_dec(v___y_2149_);
                        v___x_2162_ = lean_string_append(v___x_2160_, v___x_2161_);
                        lean_dec_ref(v___x_2161_);
                        v___y_2132_ = v___y_2146_;
                        v___y_2133_ = v___y_2147_;
                        v___y_2134_ = v_right_2159_;
                        v___y_2135_ = v___x_2162_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_2149_);
                        v___x_2163_ = l_Lean_JsonNumber_toString___closed__2;
                        v___y_2132_ = v___y_2146_;
                        v___y_2133_ = v___y_2147_;
                        v___y_2134_ = v_right_2159_;
                        v___y_2135_ = v___x_2163_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2150_);
                    lean_dec(v___y_2149_);
                    lean_dec(v___y_2148_);
                    lean_inc_ref(v___y_2146_);
                    v___x_2164_ = lean_string_append(v___y_2146_, v___y_2147_);
                    lean_dec_ref(v___y_2147_);
                    return v___x_2164_;
                }
            }
            3 => {
                v___x_2171_ = lean_unsigned_to_nat(10);
                v___x_2172_ = lean_nat_abs(v___y_2170_);
                v___x_2173_ = lean_nat_sub(v_exponent_2142_, v___x_2172_);
                lean_dec(v___x_2172_);
                lean_dec(v_exponent_2142_);
                v_e_x27_2174_ = lean_nat_pow(v___x_2171_, v___x_2173_);
                lean_dec(v___x_2173_);
                v___x_2175_ = lean_nat_div(v___y_2169_, v_e_x27_2174_);
                v_left_2176_ = l_Nat_reprFast(v___x_2175_);
                v___x_2177_ = lean_int_dec_eq(v___y_2170_, v___x_2166_);
                v___x_2178_ = lean_nat_mod(v___y_2169_, v_e_x27_2174_);
                lean_dec(v___y_2169_);
                v___x_2179_ = lean_nat_dec_eq(v___x_2178_, v___x_2143_);
                if v___x_2179_ == 0 {
                    v___y_2145_ = v___x_2177_;
                    v___y_2146_ = v___y_2168_;
                    v___y_2147_ = v_left_2176_;
                    v___y_2148_ = v_e_x27_2174_;
                    v___y_2149_ = v___y_2170_;
                    v___y_2150_ = v___x_2178_;
                    v___y_2151_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v___y_2145_ = v___x_2177_;
                    v___y_2146_ = v___y_2168_;
                    v___y_2147_ = v_left_2176_;
                    v___y_2148_ = v_e_x27_2174_;
                    v___y_2149_ = v___y_2170_;
                    v___y_2150_ = v___x_2178_;
                    v___y_2151_ = v___x_2177_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v_m_2182_ = lean_nat_abs(v_mantissa_2141_);
                lean_dec(v_mantissa_2141_);
                v___x_2183_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_toString___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_toString___closed__3_once),
                    _init_l_Lean_JsonNumber_toString___closed__3,
                );
                lean_inc(v_m_2182_);
                v___x_2184_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_2182_);
                v___x_2185_ = lean_nat_to_int(v___x_2184_);
                v___x_2186_ = lean_int_add(v___x_2183_, v___x_2185_);
                lean_dec(v___x_2185_);
                lean_inc(v_exponent_2142_);
                v___x_2187_ = lean_nat_to_int(v_exponent_2142_);
                v_exp_2188_ = lean_int_sub(v___x_2186_, v___x_2187_);
                lean_dec(v___x_2187_);
                lean_dec(v___x_2186_);
                v___x_2189_ = lean_int_dec_lt(v_exp_2188_, v___x_2166_);
                if v___x_2189_ == 0 {
                    lean_dec(v_exp_2188_);
                    v___y_2168_ = v___y_2181_;
                    v___y_2169_ = v_m_2182_;
                    v___y_2170_ = v___x_2166_;
                    state = 3;
                    continue;
                } else {
                    v___y_2168_ = v___y_2181_;
                    v___y_2169_ = v_m_2182_;
                    v___y_2170_ = v_exp_2188_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_shiftl(
    mut v_x_2194_: *mut LeanObject,
    mut v_x_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mantissa_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2196_ = lean_ctor_get(v_x_2194_, 0);
                v_exponent_2197_ = lean_ctor_get(v_x_2194_, 1);
                v_isSharedCheck_2210_ = (!lean_is_exclusive(v_x_2194_)) as u8;
                if v_isSharedCheck_2210_ == 0 {
                    v___x_2199_ = v_x_2194_;
                    v_isShared_2200_ = v_isSharedCheck_2210_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exponent_2197_);
                    lean_inc(v_mantissa_2196_);
                    lean_dec(v_x_2194_);
                    v___x_2199_ = lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = lean_unsigned_to_nat(10);
                v___x_2202_ = lean_nat_sub(v_x_2195_, v_exponent_2197_);
                v___x_2203_ = lean_nat_pow(v___x_2201_, v___x_2202_);
                lean_dec(v___x_2202_);
                v___x_2204_ = lean_nat_to_int(v___x_2203_);
                v___x_2205_ = lean_int_mul(v_mantissa_2196_, v___x_2204_);
                lean_dec(v___x_2204_);
                lean_dec(v_mantissa_2196_);
                v___x_2206_ = lean_nat_sub(v_exponent_2197_, v_x_2195_);
                lean_dec(v_exponent_2197_);
                if v_isShared_2200_ == 0 {
                    lean_ctor_set(v___x_2199_, 1, v___x_2206_);
                    lean_ctor_set(v___x_2199_, 0, v___x_2205_);
                    v___x_2208_ = v___x_2199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2205_);
                    lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2206_);
                    v___x_2208_ = v_reuseFailAlloc_2209_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_shiftl___boxed(
    mut v_x_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2213_: *mut LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Lean_JsonNumber_shiftl(v_x_2211_, v_x_2212_);
    lean_dec(v_x_2212_);
    return v_res_2213_;
}
pub unsafe fn l_Lean_JsonNumber_shiftr(
    mut v_x_2214_: *mut LeanObject,
    mut v_x_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mantissa_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2216_ = lean_ctor_get(v_x_2214_, 0);
                v_exponent_2217_ = lean_ctor_get(v_x_2214_, 1);
                v_isSharedCheck_2225_ = (!lean_is_exclusive(v_x_2214_)) as u8;
                if v_isSharedCheck_2225_ == 0 {
                    v___x_2219_ = v_x_2214_;
                    v_isShared_2220_ = v_isSharedCheck_2225_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exponent_2217_);
                    lean_inc(v_mantissa_2216_);
                    lean_dec(v_x_2214_);
                    v___x_2219_ = lean_box(0);
                    v_isShared_2220_ = v_isSharedCheck_2225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2221_ = lean_nat_add(v_exponent_2217_, v_x_2215_);
                lean_dec(v_exponent_2217_);
                if v_isShared_2220_ == 0 {
                    lean_ctor_set(v___x_2219_, 1, v___x_2221_);
                    v___x_2223_ = v___x_2219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_mantissa_2216_);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2221_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_shiftr___boxed(
    mut v_x_2226_: *mut LeanObject,
    mut v_x_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_JsonNumber_shiftr(v_x_2226_, v_x_2227_);
    lean_dec(v_x_2227_);
    return v_res_2228_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4() -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lean_JsonNumber_instRepr___lam__0___closed__0;
    v___x_2237_ = lean_string_length(v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5() -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__4_once),
        _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4,
    );
    v___x_2239_ = lean_nat_to_int(v___x_2238_);
    return v___x_2239_;
}
pub unsafe fn l_Lean_JsonNumber_instRepr___lam__0(
    mut v_x_2244_: *mut LeanObject,
    mut v_x_2245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mantissa_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___y_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2246_ = lean_ctor_get(v_x_2244_, 0);
                v_exponent_2247_ = lean_ctor_get(v_x_2244_, 1);
                v_isSharedCheck_2276_ = (!lean_is_exclusive(v_x_2244_)) as u8;
                if v_isSharedCheck_2276_ == 0 {
                    v___x_2249_ = v_x_2244_;
                    v_isShared_2250_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exponent_2247_);
                    lean_inc(v_mantissa_2246_);
                    lean_dec(v_x_2244_);
                    v___x_2249_ = lean_box(0);
                    v_isShared_2250_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2268_ = lean_unsigned_to_nat(0);
                v___x_2269_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2270_ = lean_int_dec_lt(v_mantissa_2246_, v___x_2269_);
                if v___x_2270_ == 0 {
                    v___x_2271_ = l_Int_repr(v_mantissa_2246_);
                    lean_dec(v_mantissa_2246_);
                    v___x_2272_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2272_, 0, v___x_2271_);
                    v___y_2252_ = v___x_2272_;
                    state = 2;
                    continue;
                } else {
                    v___x_2273_ = l_Int_repr(v_mantissa_2246_);
                    lean_dec(v_mantissa_2246_);
                    v___x_2274_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v___x_2274_, 0, v___x_2273_);
                    v___x_2275_ = l_Repr_addAppParen(v___x_2274_, v___x_2268_);
                    v___y_2252_ = v___x_2275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2253_ = l_Lean_JsonNumber_instRepr___lam__0___closed__2;
                if v_isShared_2250_ == 0 {
                    lean_ctor_set_tag(v___x_2249_, 5);
                    lean_ctor_set(v___x_2249_, 1, v___x_2253_);
                    lean_ctor_set(v___x_2249_, 0, v___y_2252_);
                    v___x_2255_ = v___x_2249_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___y_2252_);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2253_);
                    v___x_2255_ = v_reuseFailAlloc_2267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2256_ = l_Nat_reprFast(v_exponent_2247_);
                v___x_2257_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_2257_, 0, v___x_2256_);
                v___x_2258_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2258_, 0, v___x_2255_);
                lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                v___x_2259_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__5_once),
                    _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5,
                );
                v___x_2260_ = l_Lean_JsonNumber_instRepr___lam__0___closed__6;
                v___x_2261_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2261_, 0, v___x_2260_);
                lean_ctor_set(v___x_2261_, 1, v___x_2258_);
                v___x_2262_ = l_Lean_JsonNumber_instRepr___lam__0___closed__7;
                v___x_2263_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_2263_, 0, v___x_2261_);
                lean_ctor_set(v___x_2263_, 1, v___x_2262_);
                v___x_2264_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_2264_, 0, v___x_2259_);
                lean_ctor_set(v___x_2264_, 1, v___x_2263_);
                v___x_2265_ = 0;
                v___x_2266_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_2266_, 0, v___x_2264_);
                lean_ctor_set_uint8(
                    v___x_2266_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2265_,
                );
                return v___x_2266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_instRepr___lam__0___boxed(
    mut v_x_2277_: *mut LeanObject,
    mut v_x_2278_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2279_: *mut LeanObject = core::ptr::null_mut();
    v_res_2279_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_2277_, v_x_2278_);
    lean_dec(v_x_2278_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_JsonNumber_instOfScientific___lam__0(
    mut v_mantissa_2282_: *mut LeanObject,
    mut v_exponentSign_2283_: u8,
    mut v_decimalExponent_2284_: *mut LeanObject,
) -> *mut LeanObject {
    if v_exponentSign_2283_ == 0 {
        let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
        v___x_2285_ = lean_unsigned_to_nat(10);
        v___x_2286_ = lean_nat_pow(v___x_2285_, v_decimalExponent_2284_);
        lean_dec(v_decimalExponent_2284_);
        v___x_2287_ = lean_nat_mul(v_mantissa_2282_, v___x_2286_);
        lean_dec(v___x_2286_);
        lean_dec(v_mantissa_2282_);
        v___x_2288_ = lean_nat_to_int(v___x_2287_);
        v___x_2289_ = lean_unsigned_to_nat(0);
        v___x_2290_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2290_, 0, v___x_2288_);
        lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        return v___x_2290_;
    } else {
        let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
        v___x_2291_ = lean_nat_to_int(v_mantissa_2282_);
        v___x_2292_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2292_, 0, v___x_2291_);
        lean_ctor_set(v___x_2292_, 1, v_decimalExponent_2284_);
        return v___x_2292_;
    }
}
pub unsafe fn l_Lean_JsonNumber_instOfScientific___lam__0___boxed(
    mut v_mantissa_2293_: *mut LeanObject,
    mut v_exponentSign_2294_: *mut LeanObject,
    mut v_decimalExponent_2295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exponentSign_boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut LeanObject = core::ptr::null_mut();
    v_exponentSign_boxed_2296_ = (lean_unbox(v_exponentSign_2294_) as u8);
    v_res_2297_ = l_Lean_JsonNumber_instOfScientific___lam__0(
        v_mantissa_2293_,
        v_exponentSign_boxed_2296_,
        v_decimalExponent_2295_,
    );
    return v_res_2297_;
}
pub unsafe fn l_Lean_JsonNumber_instNeg___lam__0(
    mut v_jn_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_mantissa_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2301_ = lean_ctor_get(v_jn_2300_, 0);
                v_exponent_2302_ = lean_ctor_get(v_jn_2300_, 1);
                v_isSharedCheck_2310_ = (!lean_is_exclusive(v_jn_2300_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v___x_2304_ = v_jn_2300_;
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exponent_2302_);
                    lean_inc(v_mantissa_2301_);
                    lean_dec(v_jn_2300_);
                    v___x_2304_ = lean_box(0);
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2306_ = lean_int_neg(v_mantissa_2301_);
                lean_dec(v_mantissa_2301_);
                if v_isShared_2305_ == 0 {
                    lean_ctor_set(v___x_2304_, 0, v___x_2306_);
                    v___x_2308_ = v___x_2304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
                    lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_exponent_2302_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_JsonNumber_instInhabited___closed__0() -> *mut LeanObject {
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    v___x_2313_ = lean_unsigned_to_nat(0);
    v___x_2314_ = l_Lean_JsonNumber_fromNat(v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instInhabited() -> *mut LeanObject {
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2315_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0_once),
        _init_l_Lean_JsonNumber_instInhabited___closed__0,
    );
    return v___x_2315_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toFloat___closed__0() -> f64 {
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: f64 = 0.0;
    v___x_2316_ = lean_unsigned_to_nat(1);
    v___x_2317_ = 1;
    v___x_2318_ = lean_unsigned_to_nat(10);
    v___x_2319_ = l_Float_ofScientific(v___x_2318_, v___x_2317_, v___x_2316_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toFloat___closed__1() -> f64 {
    let mut v___x_2320_: f64 = 0.0;
    let mut v___x_2321_: f64 = 0.0;
    v___x_2320_ = lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__0_once),
        _init_l_Lean_JsonNumber_toFloat___closed__0,
    );
    v___x_2321_ = lean_float_negate(v___x_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_JsonNumber_toFloat(mut v_x_2322_: *mut LeanObject) -> f64 {
    let mut v_mantissa_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: f64 = 0.0;
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: f64 = 0.0;
    let mut v___x_2330_: f64 = 0.0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: f64 = 0.0;
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: f64 = 0.0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2323_ = lean_ctor_get(v_x_2322_, 0);
                lean_inc(v_mantissa_2323_);
                v_exponent_2324_ = lean_ctor_get(v_x_2322_, 1);
                lean_inc(v_exponent_2324_);
                lean_dec_ref(v_x_2322_);
                v___x_2331_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2332_ = lean_int_dec_le(v___x_2331_, v_mantissa_2323_);
                if v___x_2332_ == 0 {
                    v___x_2333_ = lean_float_once(
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__1_once),
                        _init_l_Lean_JsonNumber_toFloat___closed__1,
                    );
                    v___y_2326_ = v___x_2333_;
                    state = 1;
                    continue;
                } else {
                    v___x_2334_ = lean_unsigned_to_nat(10);
                    v___x_2335_ = lean_unsigned_to_nat(1);
                    v___x_2336_ = l_Float_ofScientific(v___x_2334_, v___x_2332_, v___x_2335_);
                    v___y_2326_ = v___x_2336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2327_ = lean_nat_abs(v_mantissa_2323_);
                lean_dec(v_mantissa_2323_);
                v___x_2328_ = 1;
                v___x_2329_ = l_Float_ofScientific(v___x_2327_, v___x_2328_, v_exponent_2324_);
                lean_dec(v___x_2327_);
                v___x_2330_ = lean_float_mul(v___y_2326_, v___x_2329_);
                return v___x_2330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_toFloat___boxed(mut v_x_2337_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2338_: f64 = 0.0;
    let mut v_r_2339_: *mut LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_JsonNumber_toFloat(v_x_2337_);
    v_r_2339_ = lean_box_float(v_res_2338_);
    return v_r_2339_;
}
pub unsafe fn l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(
    mut v_msg_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Lean_JsonNumber_instInhabited;
    v___x_2342_ = lean_panic_fn_borrowed(v___x_2341_, v_msg_2340_);
    return v___x_2342_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(
    mut v_x_2346_: f64,
) -> *mut LeanObject {
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v_fst_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_unused_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_unused_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2347_ = lean_float_to_string(v_x_2346_);
                v___x_2348_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_2347_);
                if lean_obj_tag(v___x_2348_) == 0 {
                    v___x_2349_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
                    v___x_2350_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1;
                    v___x_2351_ = lean_unsigned_to_nat(160);
                    v___x_2352_ = lean_unsigned_to_nat(12);
                    v___x_2353_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2;
                    v___x_2354_ = lean_string_append(v___x_2353_, v___x_2347_);
                    lean_dec_ref(v___x_2347_);
                    v___x_2355_ = l_mkPanicMessageWithDecl(
                        v___x_2349_,
                        v___x_2350_,
                        v___x_2351_,
                        v___x_2352_,
                        v___x_2354_,
                    );
                    lean_dec_ref(v___x_2354_);
                    v___x_2356_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_2355_);
                    return v___x_2356_;
                } else {
                    lean_dec_ref(v___x_2347_);
                    v_val_2357_ = lean_ctor_get(v___x_2348_, 0);
                    lean_inc(v_val_2357_);
                    lean_dec_ref_known(v___x_2348_, 1);
                    v_snd_2358_ = lean_ctor_get(v_val_2357_, 1);
                    lean_inc(v_snd_2358_);
                    v_fst_2359_ = lean_ctor_get(v_snd_2358_, 0);
                    v___x_2360_ = (lean_unbox(v_fst_2359_) as u8);
                    if v___x_2360_ == 0 {
                        v_fst_2361_ = lean_ctor_get(v_val_2357_, 0);
                        lean_inc(v_fst_2361_);
                        lean_dec(v_val_2357_);
                        v_snd_2362_ = lean_ctor_get(v_snd_2358_, 1);
                        v_isSharedCheck_2374_ = (!lean_is_exclusive(v_snd_2358_)) as u8;
                        if v_isSharedCheck_2374_ == 0 {
                            v_unused_2375_ = lean_ctor_get(v_snd_2358_, 0);
                            lean_dec(v_unused_2375_);
                            v___x_2364_ = v_snd_2358_;
                            v_isShared_2365_ = v_isSharedCheck_2374_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_2362_);
                            lean_dec(v_snd_2358_);
                            v___x_2364_ = lean_box(0);
                            v_isShared_2365_ = v_isSharedCheck_2374_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_fst_2376_ = lean_ctor_get(v_val_2357_, 0);
                        lean_inc(v_fst_2376_);
                        lean_dec(v_val_2357_);
                        v_snd_2377_ = lean_ctor_get(v_snd_2358_, 1);
                        v_isSharedCheck_2385_ = (!lean_is_exclusive(v_snd_2358_)) as u8;
                        if v_isSharedCheck_2385_ == 0 {
                            v_unused_2386_ = lean_ctor_get(v_snd_2358_, 0);
                            lean_dec(v_unused_2386_);
                            v___x_2379_ = v_snd_2358_;
                            v_isShared_2380_ = v_isSharedCheck_2385_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_snd_2377_);
                            lean_dec(v_snd_2358_);
                            v___x_2379_ = lean_box(0);
                            v_isShared_2380_ = v_isSharedCheck_2385_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2366_ = lean_unsigned_to_nat(10);
                v___x_2367_ = lean_nat_pow(v___x_2366_, v_snd_2362_);
                lean_dec(v_snd_2362_);
                v___x_2368_ = lean_nat_mul(v_fst_2361_, v___x_2367_);
                lean_dec(v___x_2367_);
                lean_dec(v_fst_2361_);
                v___x_2369_ = lean_nat_to_int(v___x_2368_);
                v___x_2370_ = lean_unsigned_to_nat(0);
                if v_isShared_2365_ == 0 {
                    lean_ctor_set(v___x_2364_, 1, v___x_2370_);
                    lean_ctor_set(v___x_2364_, 0, v___x_2369_);
                    v___x_2372_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2369_);
                    lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2370_);
                    v___x_2372_ = v_reuseFailAlloc_2373_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2372_;
            }
            3 => {
                v___x_2381_ = lean_nat_to_int(v_fst_2376_);
                if v_isShared_2380_ == 0 {
                    lean_ctor_set(v___x_2379_, 0, v___x_2381_);
                    v___x_2383_ = v___x_2379_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
                    lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_snd_2377_);
                    v___x_2383_ = v_reuseFailAlloc_2384_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___boxed(
    mut v_x_2387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2388_: f64 = 0.0;
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2388_ = lean_unbox_float(v_x_2387_);
    lean_dec_ref(v_x_2387_);
    v_res_2389_ =
        l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_2388_);
    return v_res_2389_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0() -> f64 {
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: f64 = 0.0;
    v___x_2390_ = lean_unsigned_to_nat(1);
    v___x_2391_ = 1;
    v___x_2392_ = lean_unsigned_to_nat(0);
    v___x_2393_ = l_Float_ofScientific(v___x_2392_, v___x_2391_, v___x_2390_);
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1() -> *mut LeanObject {
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    v___x_2394_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0_once),
        _init_l_Lean_JsonNumber_instInhabited___closed__0,
    );
    v___x_2395_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2395_, 0, v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2() -> f64 {
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: f64 = 0.0;
    v___x_2396_ = lean_unsigned_to_nat(0);
    v___x_2397_ = lean_float_of_nat(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Lean_JsonNumber_fromFloat_x3f(mut v_x_2407_: f64) -> *mut LeanObject {
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: f64 = 0.0;
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: f64 = 0.0;
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mantissa_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: f64 = 0.0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2408_ = lean_float_isnan(v_x_2407_);
                if v___x_2408_ == 0 {
                    v___x_2409_ = lean_float_isinf(v_x_2407_);
                    if v___x_2409_ == 0 {
                        v___x_2410_ = lean_float_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_fromFloat_x3f___closed__0),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonNumber_fromFloat_x3f___closed__0_once
                            ),
                            _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0,
                        );
                        v___x_2411_ = lean_float_beq(v_x_2407_, v___x_2410_);
                        if v___x_2411_ == 0 {
                            v___x_2412_ = lean_float_decLt(v_x_2407_, v___x_2410_);
                            if v___x_2412_ == 0 {
                                v___x_2413_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_2407_);
                                v___x_2414_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                                return v___x_2414_;
                            } else {
                                v___x_2415_ = lean_float_negate(v_x_2407_);
                                v___x_2416_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_2415_);
                                v_mantissa_2417_ = lean_ctor_get(v___x_2416_, 0);
                                v_exponent_2418_ = lean_ctor_get(v___x_2416_, 1);
                                v_isSharedCheck_2427_ = (!lean_is_exclusive(v___x_2416_)) as u8;
                                if v_isSharedCheck_2427_ == 0 {
                                    v___x_2420_ = v___x_2416_;
                                    v_isShared_2421_ = v_isSharedCheck_2427_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_exponent_2418_);
                                    lean_inc(v_mantissa_2417_);
                                    lean_dec(v___x_2416_);
                                    v___x_2420_ = lean_box(0);
                                    v_isShared_2421_ = v_isSharedCheck_2427_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2428_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonNumber_fromFloat_x3f___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_JsonNumber_fromFloat_x3f___closed__1_once
                                ),
                                _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1,
                            );
                            return v___x_2428_;
                        }
                    } else {
                        v___x_2429_ = lean_float_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_fromFloat_x3f___closed__2),
                            core::ptr::addr_of_mut!(
                                l_Lean_JsonNumber_fromFloat_x3f___closed__2_once
                            ),
                            _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2,
                        );
                        v___x_2430_ = lean_float_decLt(v___x_2429_, v_x_2407_);
                        if v___x_2430_ == 0 {
                            v___x_2431_ = l_Lean_JsonNumber_fromFloat_x3f___closed__4;
                            return v___x_2431_;
                        } else {
                            v___x_2432_ = l_Lean_JsonNumber_fromFloat_x3f___closed__6;
                            return v___x_2432_;
                        }
                    }
                } else {
                    v___x_2433_ = l_Lean_JsonNumber_fromFloat_x3f___closed__8;
                    return v___x_2433_;
                }
            }
            1 => {
                v___x_2422_ = lean_int_neg(v_mantissa_2417_);
                lean_dec(v_mantissa_2417_);
                if v_isShared_2421_ == 0 {
                    lean_ctor_set(v___x_2420_, 0, v___x_2422_);
                    v___x_2424_ = v___x_2420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_exponent_2418_);
                    v___x_2424_ = v_reuseFailAlloc_2426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2425_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_fromFloat_x3f___boxed(
    mut v_x_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_2435_: f64 = 0.0;
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_2435_ = lean_unbox_float(v_x_2434_);
    lean_dec_ref(v_x_2434_);
    v_res_2436_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_2435_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_strLt(mut v_a_2437_: *mut LeanObject, mut v_b_2438_: *mut LeanObject) -> u8 {
    let mut v___x_2439_: u8 = 0;
    v___x_2439_ = lean_string_dec_lt(v_a_2437_, v_b_2438_);
    return v___x_2439_;
}
pub unsafe fn l_Lean_strLt___boxed(
    mut v_a_2440_: *mut LeanObject,
    mut v_b_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2442_: u8 = 0;
    let mut v_r_2443_: *mut LeanObject = core::ptr::null_mut();
    v_res_2442_ = l_Lean_strLt(v_a_2440_, v_b_2441_);
    lean_dec_ref(v_b_2441_);
    lean_dec_ref(v_a_2440_);
    v_r_2443_ = lean_box((v_res_2442_) as usize);
    return v_r_2443_;
}
pub unsafe fn l_Lean_Json_ctorIdx(mut v_x_2444_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_2444_) {
        0 => {
            let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
            v___x_2445_ = lean_unsigned_to_nat(0);
            return v___x_2445_;
        }
        1 => {
            let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
            v___x_2446_ = lean_unsigned_to_nat(1);
            return v___x_2446_;
        }
        2 => {
            let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
            v___x_2447_ = lean_unsigned_to_nat(2);
            return v___x_2447_;
        }
        3 => {
            let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
            v___x_2448_ = lean_unsigned_to_nat(3);
            return v___x_2448_;
        }
        4 => {
            let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
            v___x_2449_ = lean_unsigned_to_nat(4);
            return v___x_2449_;
        }
        _ => {
            let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
            v___x_2450_ = lean_unsigned_to_nat(5);
            return v___x_2450_;
        }
    }
}
pub unsafe fn l_Lean_Json_ctorIdx___boxed(mut v_x_2451_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_2452_: *mut LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_Lean_Json_ctorIdx(v_x_2451_);
    lean_dec(v_x_2451_);
    return v_res_2452_;
}
pub unsafe fn l_Lean_Json_ctorElim___redArg(
    mut v_t_2453_: *mut LeanObject,
    mut v_k_2454_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_2453_) {
        0 => {
            return v_k_2454_;
        }
        1 => {
            let mut v_b_2455_: u8 = 0;
            let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
            v_b_2455_ = lean_ctor_get_uint8(v_t_2453_, 0 as u32);
            lean_dec_ref_known(v_t_2453_, 0);
            v___x_2456_ = lean_box((v_b_2455_) as usize);
            v___x_2457_ = lean_apply_1(v_k_2454_, v___x_2456_);
            return v___x_2457_;
        }
        5 => {
            let mut v_kvPairs_2458_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
            v_kvPairs_2458_ = lean_ctor_get(v_t_2453_, 0);
            lean_inc(v_kvPairs_2458_);
            lean_dec_ref_known(v_t_2453_, 1);
            v___x_2459_ = lean_apply_1(v_k_2454_, v_kvPairs_2458_);
            return v___x_2459_;
        }
        _ => {
            let mut v_n_2460_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
            v_n_2460_ = lean_ctor_get(v_t_2453_, 0);
            lean_inc_ref(v_n_2460_);
            lean_dec(v_t_2453_);
            v___x_2461_ = lean_apply_1(v_k_2454_, v_n_2460_);
            return v___x_2461_;
        }
    }
}
pub unsafe fn l_Lean_Json_ctorElim(
    mut v_motive__1_2462_: *mut LeanObject,
    mut v_ctorIdx_2463_: *mut LeanObject,
    mut v_t_2464_: *mut LeanObject,
    mut v_h_2465_: *mut LeanObject,
    mut v_k_2466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = l_Lean_Json_ctorElim___redArg(v_t_2464_, v_k_2466_);
    return v___x_2467_;
}
pub unsafe fn l_Lean_Json_ctorElim___boxed(
    mut v_motive__1_2468_: *mut LeanObject,
    mut v_ctorIdx_2469_: *mut LeanObject,
    mut v_t_2470_: *mut LeanObject,
    mut v_h_2471_: *mut LeanObject,
    mut v_k_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2473_: *mut LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Json_ctorElim(
        v_motive__1_2468_,
        v_ctorIdx_2469_,
        v_t_2470_,
        v_h_2471_,
        v_k_2472_,
    );
    lean_dec(v_ctorIdx_2469_);
    return v_res_2473_;
}
pub unsafe fn l_Lean_Json_null_elim___redArg(
    mut v_t_2474_: *mut LeanObject,
    mut v_null_2475_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_Json_ctorElim___redArg(v_t_2474_, v_null_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_Json_null_elim(
    mut v_motive__1_2477_: *mut LeanObject,
    mut v_t_2478_: *mut LeanObject,
    mut v_h_2479_: *mut LeanObject,
    mut v_null_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    v___x_2481_ = l_Lean_Json_ctorElim___redArg(v_t_2478_, v_null_2480_);
    return v___x_2481_;
}
pub unsafe fn l_Lean_Json_bool_elim___redArg(
    mut v_t_2482_: *mut LeanObject,
    mut v_bool_2483_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    v___x_2484_ = l_Lean_Json_ctorElim___redArg(v_t_2482_, v_bool_2483_);
    return v___x_2484_;
}
pub unsafe fn l_Lean_Json_bool_elim(
    mut v_motive__1_2485_: *mut LeanObject,
    mut v_t_2486_: *mut LeanObject,
    mut v_h_2487_: *mut LeanObject,
    mut v_bool_2488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_Json_ctorElim___redArg(v_t_2486_, v_bool_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_Json_num_elim___redArg(
    mut v_t_2490_: *mut LeanObject,
    mut v_num_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Lean_Json_ctorElim___redArg(v_t_2490_, v_num_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Json_num_elim(
    mut v_motive__1_2493_: *mut LeanObject,
    mut v_t_2494_: *mut LeanObject,
    mut v_h_2495_: *mut LeanObject,
    mut v_num_2496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Lean_Json_ctorElim___redArg(v_t_2494_, v_num_2496_);
    return v___x_2497_;
}
pub unsafe fn l_Lean_Json_str_elim___redArg(
    mut v_t_2498_: *mut LeanObject,
    mut v_str_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    v___x_2500_ = l_Lean_Json_ctorElim___redArg(v_t_2498_, v_str_2499_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_Json_str_elim(
    mut v_motive__1_2501_: *mut LeanObject,
    mut v_t_2502_: *mut LeanObject,
    mut v_h_2503_: *mut LeanObject,
    mut v_str_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_Lean_Json_ctorElim___redArg(v_t_2502_, v_str_2504_);
    return v___x_2505_;
}
pub unsafe fn l_Lean_Json_arr_elim___redArg(
    mut v_t_2506_: *mut LeanObject,
    mut v_arr_2507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Json_ctorElim___redArg(v_t_2506_, v_arr_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_Json_arr_elim(
    mut v_motive__1_2509_: *mut LeanObject,
    mut v_t_2510_: *mut LeanObject,
    mut v_h_2511_: *mut LeanObject,
    mut v_arr_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Lean_Json_ctorElim___redArg(v_t_2510_, v_arr_2512_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_Json_obj_elim___redArg(
    mut v_t_2514_: *mut LeanObject,
    mut v_obj_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Json_ctorElim___redArg(v_t_2514_, v_obj_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Json_obj_elim(
    mut v_motive__1_2517_: *mut LeanObject,
    mut v_t_2518_: *mut LeanObject,
    mut v_h_2519_: *mut LeanObject,
    mut v_obj_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Json_ctorElim___redArg(v_t_2518_, v_obj_2520_);
    return v___x_2521_;
}
pub unsafe fn _init_l_Lean_instInhabitedJson_default() -> *mut LeanObject {
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    v___x_2522_ = lean_box(0);
    return v___x_2522_;
}
pub unsafe fn _init_l_Lean_instInhabitedJson() -> *mut LeanObject {
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    v___x_2523_ = lean_box(0);
    return v___x_2523_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(
    mut v_init_2524_: *mut LeanObject,
    mut v_x_2525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2525_) == 0 {
                    v_l_2526_ = lean_ctor_get(v_x_2525_, 3);
                    v_r_2527_ = lean_ctor_get(v_x_2525_, 4);
                    v___x_2528_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2524_, v_l_2526_);
                    v___x_2529_ = lean_unsigned_to_nat(1);
                    v___x_2530_ = lean_nat_add(v___x_2528_, v___x_2529_);
                    lean_dec(v___x_2528_);
                    v_init_2524_ = v___x_2530_;
                    v_x_2525_ = v_r_2527_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2524_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1___boxed(
    mut v_init_2532_: *mut LeanObject,
    mut v_x_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2534_: *mut LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2532_, v_x_2533_);
    lean_dec(v_x_2533_);
    return v_res_2534_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(
    mut v_t_2535_: *mut LeanObject,
    mut v_k_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2535_) == 0 {
                    v_k_2537_ = lean_ctor_get(v_t_2535_, 1);
                    v_v_2538_ = lean_ctor_get(v_t_2535_, 2);
                    v_l_2539_ = lean_ctor_get(v_t_2535_, 3);
                    v_r_2540_ = lean_ctor_get(v_t_2535_, 4);
                    v___x_2541_ = lean_string_compare(v_k_2536_, v_k_2537_);
                    match v___x_2541_ {
                        0 => {
                            v_t_2535_ = v_l_2539_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2538_);
                            v___x_2543_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2543_, 0, v_v_2538_);
                            return v___x_2543_;
                        }
                        _ => {
                            v_t_2535_ = v_r_2540_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2545_ = lean_box(0);
                    return v___x_2545_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(
    mut v_t_2546_: *mut LeanObject,
    mut v_k_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2548_: *mut LeanObject = core::ptr::null_mut();
    v_res_2548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_2546_, v_k_2547_);
    lean_dec_ref(v_k_2547_);
    lean_dec(v_t_2546_);
    return v_res_2548_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(
    mut v_kvPairs_2552_: *mut LeanObject,
    mut v_init_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2565_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v_val_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_unused_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2554_) == 0 {
                    v_k_2555_ = lean_ctor_get(v_x_2554_, 1);
                    v_v_2556_ = lean_ctor_get(v_x_2554_, 2);
                    v_l_2557_ = lean_ctor_get(v_x_2554_, 3);
                    v_r_2558_ = lean_ctor_get(v_x_2554_, 4);
                    v___x_2559_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2552_, v_init_2553_, v_l_2557_);
                    if lean_obj_tag(v___x_2559_) == 0 {
                        return v___x_2559_;
                    } else {
                        v_isSharedCheck_2578_ = (!lean_is_exclusive(v___x_2559_)) as u8;
                        if v_isSharedCheck_2578_ == 0 {
                            v_unused_2579_ = lean_ctor_get(v___x_2559_, 0);
                            lean_dec(v_unused_2579_);
                            v___x_2561_ = v___x_2559_;
                            v_isShared_2562_ = v_isSharedCheck_2578_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2559_);
                            v___x_2561_ = lean_box(0);
                            v_isShared_2562_ = v_isSharedCheck_2578_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2580_, 0, v_init_2553_);
                    return v___x_2580_;
                }
            }
            1 => {
                v___x_2563_ = lean_box(0);
                v___x_2572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_2552_, v_k_2555_);
                if lean_obj_tag(v___x_2572_) == 0 {
                    v___x_2573_ = 0;
                    v___y_2565_ = v___x_2573_;
                    state = 2;
                    continue;
                } else {
                    v_val_2574_ = lean_ctor_get(v___x_2572_, 0);
                    lean_inc(v_val_2574_);
                    lean_dec_ref_known(v___x_2572_, 1);
                    v___x_2575_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(
                        v_v_2556_,
                        v_val_2574_,
                    );
                    lean_dec(v_val_2574_);
                    if v___x_2575_ == 0 {
                        v___y_2565_ = v___x_2575_;
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_2561_);
                        v___x_2576_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0;
                        v_init_2553_ = v___x_2576_;
                        v_x_2554_ = v_r_2558_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2566_ = lean_box((v___y_2565_) as usize);
                v___x_2567_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                v___x_2568_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                lean_ctor_set(v___x_2568_, 1, v___x_2563_);
                if v_isShared_2562_ == 0 {
                    lean_ctor_set_tag(v___x_2561_, 0);
                    lean_ctor_set(v___x_2561_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2561_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2571_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(
    mut v_x_2581_: *mut LeanObject,
    mut v_x_2582_: *mut LeanObject,
) -> u8 {
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: u8 = 0;
    let mut v_b_2585_: u8 = 0;
    let mut v_b_2586_: u8 = 0;
    let mut v___x_2587_: u8 = 0;
    let mut v_b_2588_: u8 = 0;
    let mut v___x_2589_: u8 = 0;
    let mut v_n_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut v_s_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: u8 = 0;
    let mut v___x_2597_: u8 = 0;
    let mut v_elems_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elems_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u8 = 0;
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: u8 = 0;
    let mut v_kvPairs_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_szA_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_szB_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    let mut v___y_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_2581_) {
                0 => {
                    if lean_obj_tag(v_x_2582_) == 0 {
                        v___x_2583_ = 1;
                        return v___x_2583_;
                    } else {
                        v___x_2584_ = 0;
                        return v___x_2584_;
                    }
                }
                1 => {
                    if lean_obj_tag(v_x_2582_) == 1 {
                        v_b_2585_ = lean_ctor_get_uint8(v_x_2581_, 0 as u32);
                        if v_b_2585_ == 0 {
                            v_b_2586_ = lean_ctor_get_uint8(v_x_2582_, 0 as u32);
                            if v_b_2586_ == 0 {
                                v___x_2587_ = 1;
                                return v___x_2587_;
                            } else {
                                return v_b_2585_;
                            }
                        } else {
                            v_b_2588_ = lean_ctor_get_uint8(v_x_2582_, 0 as u32);
                            return v_b_2588_;
                        }
                    } else {
                        v___x_2589_ = 0;
                        return v___x_2589_;
                    }
                }
                2 => {
                    if lean_obj_tag(v_x_2582_) == 2 {
                        v_n_2590_ = lean_ctor_get(v_x_2581_, 0);
                        v_n_2591_ = lean_ctor_get(v_x_2582_, 0);
                        v___x_2592_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_2590_, v_n_2591_);
                        return v___x_2592_;
                    } else {
                        v___x_2593_ = 0;
                        return v___x_2593_;
                    }
                }
                3 => {
                    if lean_obj_tag(v_x_2582_) == 3 {
                        v_s_2594_ = lean_ctor_get(v_x_2581_, 0);
                        v_s_2595_ = lean_ctor_get(v_x_2582_, 0);
                        v___x_2596_ = lean_string_dec_eq(v_s_2594_, v_s_2595_);
                        return v___x_2596_;
                    } else {
                        v___x_2597_ = 0;
                        return v___x_2597_;
                    }
                }
                4 => {
                    if lean_obj_tag(v_x_2582_) == 4 {
                        v_elems_2598_ = lean_ctor_get(v_x_2581_, 0);
                        v_elems_2599_ = lean_ctor_get(v_x_2582_, 0);
                        v___x_2600_ = lean_array_get_size(v_elems_2598_);
                        v___x_2601_ = lean_array_get_size(v_elems_2599_);
                        v___x_2602_ = lean_nat_dec_eq(v___x_2600_, v___x_2601_);
                        if v___x_2602_ == 0 {
                            return v___x_2602_;
                        } else {
                            v___x_2603_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_elems_2598_, v_elems_2599_, v___x_2600_);
                            return v___x_2603_;
                        }
                    } else {
                        v___x_2604_ = 0;
                        return v___x_2604_;
                    }
                }
                _ => {
                    if lean_obj_tag(v_x_2582_) == 5 {
                        v_kvPairs_2605_ = lean_ctor_get(v_x_2581_, 0);
                        v_kvPairs_2606_ = lean_ctor_get(v_x_2582_, 0);
                        v___x_2607_ = lean_unsigned_to_nat(0);
                        v_szA_2608_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_2607_, v_kvPairs_2605_);
                        v_szB_2609_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_2607_, v_kvPairs_2606_);
                        v___x_2610_ = lean_nat_dec_eq(v_szA_2608_, v_szB_2609_);
                        lean_dec(v_szB_2609_);
                        lean_dec(v_szA_2608_);
                        if v___x_2610_ == 0 {
                            return v___x_2610_;
                        } else {
                            v___x_2616_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0;
                            v___x_2617_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2606_, v___x_2616_, v_kvPairs_2605_);
                            v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
                            lean_inc(v_a_2618_);
                            lean_dec_ref(v___x_2617_);
                            v___y_2612_ = v_a_2618_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2619_ = 0;
                        return v___x_2619_;
                    }
                }
            },
            1 => {
                v_fst_2613_ = lean_ctor_get(v___y_2612_, 0);
                lean_inc(v_fst_2613_);
                lean_dec_ref(v___y_2612_);
                if lean_obj_tag(v_fst_2613_) == 0 {
                    return v___x_2610_;
                } else {
                    v_val_2614_ = lean_ctor_get(v_fst_2613_, 0);
                    lean_inc(v_val_2614_);
                    lean_dec_ref_known(v_fst_2613_, 1);
                    v___x_2615_ = (lean_unbox(v_val_2614_) as u8);
                    lean_dec(v_val_2614_);
                    return v___x_2615_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(
    mut v_xs_2620_: *mut LeanObject,
    mut v_ys_2621_: *mut LeanObject,
    mut v_x_2622_: *mut LeanObject,
) -> u8 {
    let mut v_zero_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_2624_: u8 = 0;
    let mut v_one_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2623_ = lean_unsigned_to_nat(0);
                v_isZero_2624_ = lean_nat_dec_eq(v_x_2622_, v_zero_2623_);
                if v_isZero_2624_ == 1 {
                    lean_dec(v_x_2622_);
                    return v_isZero_2624_;
                } else {
                    v_one_2625_ = lean_unsigned_to_nat(1);
                    v_n_2626_ = lean_nat_sub(v_x_2622_, v_one_2625_);
                    lean_dec(v_x_2622_);
                    v___x_2627_ = lean_array_fget_borrowed(v_xs_2620_, v_n_2626_);
                    v___x_2628_ = lean_array_fget_borrowed(v_ys_2621_, v_n_2626_);
                    v___x_2629_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(
                        v___x_2627_,
                        v___x_2628_,
                    );
                    if v___x_2629_ == 0 {
                        lean_dec(v_n_2626_);
                        return v___x_2629_;
                    } else {
                        v_x_2622_ = v_n_2626_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg___boxed(
    mut v_xs_2631_: *mut LeanObject,
    mut v_ys_2632_: *mut LeanObject,
    mut v_x_2633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut LeanObject = core::ptr::null_mut();
    v_res_2634_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_2631_, v_ys_2632_, v_x_2633_);
    lean_dec_ref(v_ys_2632_);
    lean_dec_ref(v_xs_2631_);
    v_r_2635_ = lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(
    mut v_kvPairs_2636_: *mut LeanObject,
    mut v_init_2637_: *mut LeanObject,
    mut v_x_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2639_: *mut LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2636_, v_init_2637_, v_x_2638_);
    lean_dec(v_x_2638_);
    lean_dec(v_kvPairs_2636_);
    return v_res_2639_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(
    mut v_x_2640_: *mut LeanObject,
    mut v_x_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2642_: u8 = 0;
    let mut v_r_2643_: *mut LeanObject = core::ptr::null_mut();
    v_res_2642_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_2640_, v_x_2641_);
    lean_dec(v_x_2641_);
    lean_dec(v_x_2640_);
    v_r_2643_ = lean_box((v_res_2642_) as usize);
    return v_r_2643_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(
    mut v_xs_2644_: *mut LeanObject,
    mut v_ys_2645_: *mut LeanObject,
    mut v_hsz_2646_: *mut LeanObject,
    mut v_x_2647_: *mut LeanObject,
    mut v_x_2648_: *mut LeanObject,
) -> u8 {
    let mut v___x_2649_: u8 = 0;
    v___x_2649_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_2644_, v_ys_2645_, v_x_2647_);
    return v___x_2649_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(
    mut v_xs_2650_: *mut LeanObject,
    mut v_ys_2651_: *mut LeanObject,
    mut v_hsz_2652_: *mut LeanObject,
    mut v_x_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2655_: u8 = 0;
    let mut v_r_2656_: *mut LeanObject = core::ptr::null_mut();
    v_res_2655_ =
        l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(
            v_xs_2650_,
            v_ys_2651_,
            v_hsz_2652_,
            v_x_2653_,
            v_x_2654_,
        );
    lean_dec_ref(v_ys_2651_);
    lean_dec_ref(v_xs_2650_);
    v_r_2656_ = lean_box((v_res_2655_) as usize);
    return v_r_2656_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(
    mut v_init_2657_: *mut LeanObject,
    mut v_t_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    v___x_2659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2657_, v_t_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(
    mut v_init_2660_: *mut LeanObject,
    mut v_t_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2662_: *mut LeanObject = core::ptr::null_mut();
    v_res_2662_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_2660_, v_t_2661_);
    lean_dec(v_t_2661_);
    return v_res_2662_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(
    mut v_00_u03b4_2663_: *mut LeanObject,
    mut v_t_2664_: *mut LeanObject,
    mut v_k_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    v___x_2666_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_2664_, v_k_2665_);
    return v___x_2666_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(
    mut v_00_u03b4_2667_: *mut LeanObject,
    mut v_t_2668_: *mut LeanObject,
    mut v_k_2669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2670_: *mut LeanObject = core::ptr::null_mut();
    v_res_2670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_2667_, v_t_2668_, v_k_2669_);
    lean_dec_ref(v_k_2669_);
    lean_dec(v_t_2668_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_Json_instBEq___private__1(
    mut v_a_2671_: *mut LeanObject,
    mut v_a_2672_: *mut LeanObject,
) -> u8 {
    let mut v___x_2673_: u8 = 0;
    v___x_2673_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_2671_, v_a_2672_);
    return v___x_2673_;
}
pub unsafe fn l_Lean_Json_instBEq___private__1___boxed(
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2676_: u8 = 0;
    let mut v_r_2677_: *mut LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_Json_instBEq___private__1(v_a_2674_, v_a_2675_);
    lean_dec(v_a_2675_);
    lean_dec(v_a_2674_);
    v_r_2677_ = lean_box((v_res_2676_) as usize);
    return v_r_2677_;
}
pub unsafe fn _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0() -> u64 {
    let mut v___x_2680_: u64 = 0;
    let mut v___x_2681_: u64 = 0;
    v___x_2680_ = 13u64;
    v___x_2681_ = lean_uint64_mix_hash(v___x_2680_, v___x_2680_);
    return v___x_2681_;
}
pub unsafe fn _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1() -> u64 {
    let mut v___x_2682_: u64 = 0;
    let mut v___x_2683_: u64 = 0;
    let mut v___x_2684_: u64 = 0;
    v___x_2682_ = 11u64;
    v___x_2683_ = 13u64;
    v___x_2684_ = lean_uint64_mix_hash(v___x_2683_, v___x_2682_);
    return v___x_2684_;
}
pub unsafe fn _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2() -> u64 {
    let mut v___x_2685_: u64 = 0;
    let mut v___x_2686_: u64 = 0;
    let mut v___x_2687_: u64 = 0;
    v___x_2685_ = 7u64;
    v___x_2686_ = 23u64;
    v___x_2687_ = lean_uint64_mix_hash(v___x_2686_, v___x_2685_);
    return v___x_2687_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(
    mut v_as_2688_: *mut LeanObject,
    mut v_i_2689_: usize,
    mut v_stop_2690_: usize,
    mut v_b_2691_: u64,
) -> u64 {
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: u64 = 0;
    let mut v___x_2695_: u64 = 0;
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2692_ = lean_usize_dec_eq(v_i_2689_, v_stop_2690_);
                if v___x_2692_ == 0 {
                    v___x_2693_ = lean_array_uget_borrowed(v_as_2688_, v_i_2689_);
                    v___x_2694_ =
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v___x_2693_);
                    v___x_2695_ = lean_uint64_mix_hash(v_b_2691_, v___x_2694_);
                    v___x_2696_ = 1usize;
                    v___x_2697_ = lean_usize_add(v_i_2689_, v___x_2696_);
                    v_i_2689_ = v___x_2697_;
                    v_b_2691_ = v___x_2695_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2691_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(
    mut v_x_2699_: *mut LeanObject,
) -> u64 {
    match lean_obj_tag(v_x_2699_) {
        0 => {
            let mut v___x_2700_: u64 = 0;
            v___x_2700_ = 11u64;
            return v___x_2700_;
        }
        1 => {
            let mut v_b_2701_: u8 = 0;
            v_b_2701_ = lean_ctor_get_uint8(v_x_2699_, 0 as u32);
            if v_b_2701_ == 0 {
                let mut v___x_2702_: u64 = 0;
                v___x_2702_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once
                    ),
                    _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0,
                );
                return v___x_2702_;
            } else {
                let mut v___x_2703_: u64 = 0;
                v___x_2703_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once
                    ),
                    _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1,
                );
                return v___x_2703_;
            }
        }
        2 => {
            let mut v_n_2704_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2705_: u64 = 0;
            let mut v___x_2706_: u64 = 0;
            let mut v___x_2707_: u64 = 0;
            v_n_2704_ = lean_ctor_get(v_x_2699_, 0);
            v___x_2705_ = 17u64;
            v___x_2706_ = l_Lean_instHashableJsonNumber_hash(v_n_2704_);
            v___x_2707_ = lean_uint64_mix_hash(v___x_2705_, v___x_2706_);
            return v___x_2707_;
        }
        3 => {
            let mut v_s_2708_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2709_: u64 = 0;
            let mut v___x_2710_: u64 = 0;
            let mut v___x_2711_: u64 = 0;
            v_s_2708_ = lean_ctor_get(v_x_2699_, 0);
            v___x_2709_ = 19u64;
            v___x_2710_ = lean_string_hash(v_s_2708_);
            v___x_2711_ = lean_uint64_mix_hash(v___x_2709_, v___x_2710_);
            return v___x_2711_;
        }
        4 => {
            let mut v_elems_2712_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2713_: u64 = 0;
            let mut v___x_2714_: u64 = 0;
            let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2717_: u8 = 0;
            v_elems_2712_ = lean_ctor_get(v_x_2699_, 0);
            v___x_2713_ = 23u64;
            v___x_2714_ = 7u64;
            v___x_2715_ = lean_unsigned_to_nat(0);
            v___x_2716_ = lean_array_get_size(v_elems_2712_);
            v___x_2717_ = lean_nat_dec_lt(v___x_2715_, v___x_2716_);
            if v___x_2717_ == 0 {
                let mut v___x_2718_: u64 = 0;
                v___x_2718_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once
                    ),
                    _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2,
                );
                return v___x_2718_;
            } else {
                let mut v___x_2719_: u8 = 0;
                v___x_2719_ = lean_nat_dec_le(v___x_2716_, v___x_2716_);
                if v___x_2719_ == 0 {
                    if v___x_2717_ == 0 {
                        let mut v___x_2720_: u64 = 0;
                        v___x_2720_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once), _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
                        return v___x_2720_;
                    } else {
                        let mut v___x_2721_: usize = 0;
                        let mut v___x_2722_: usize = 0;
                        let mut v___x_2723_: u64 = 0;
                        let mut v___x_2724_: u64 = 0;
                        v___x_2721_ = 0usize;
                        v___x_2722_ = lean_usize_of_nat(v___x_2716_);
                        v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_2712_, v___x_2721_, v___x_2722_, v___x_2714_);
                        v___x_2724_ = lean_uint64_mix_hash(v___x_2713_, v___x_2723_);
                        return v___x_2724_;
                    }
                } else {
                    let mut v___x_2725_: usize = 0;
                    let mut v___x_2726_: usize = 0;
                    let mut v___x_2727_: u64 = 0;
                    let mut v___x_2728_: u64 = 0;
                    v___x_2725_ = 0usize;
                    v___x_2726_ = lean_usize_of_nat(v___x_2716_);
                    v___x_2727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_elems_2712_, v___x_2725_, v___x_2726_, v___x_2714_);
                    v___x_2728_ = lean_uint64_mix_hash(v___x_2713_, v___x_2727_);
                    return v___x_2728_;
                }
            }
        }
        _ => {
            let mut v_kvPairs_2729_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2730_: u64 = 0;
            let mut v___x_2731_: u64 = 0;
            let mut v___x_2732_: u64 = 0;
            let mut v___x_2733_: u64 = 0;
            v_kvPairs_2729_ = lean_ctor_get(v_x_2699_, 0);
            v___x_2730_ = 29u64;
            v___x_2731_ = 7u64;
            v___x_2732_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v___x_2731_, v_kvPairs_2729_);
            v___x_2733_ = lean_uint64_mix_hash(v___x_2730_, v___x_2732_);
            return v___x_2733_;
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(
    mut v_init_2734_: u64,
    mut v_x_2735_: *mut LeanObject,
) -> u64 {
    let mut v_k_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u64 = 0;
    let mut v___x_2741_: u64 = 0;
    let mut v___x_2742_: u64 = 0;
    let mut v___x_2743_: u64 = 0;
    let mut v___x_2744_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2735_) == 0 {
                    v_k_2736_ = lean_ctor_get(v_x_2735_, 1);
                    v_v_2737_ = lean_ctor_get(v_x_2735_, 2);
                    v_l_2738_ = lean_ctor_get(v_x_2735_, 3);
                    v_r_2739_ = lean_ctor_get(v_x_2735_, 4);
                    v___x_2740_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_2734_, v_l_2738_);
                    v___x_2741_ = lean_string_hash(v_k_2736_);
                    v___x_2742_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_v_2737_);
                    v___x_2743_ = lean_uint64_mix_hash(v___x_2741_, v___x_2742_);
                    v___x_2744_ = lean_uint64_mix_hash(v___x_2740_, v___x_2743_);
                    v_init_2734_ = v___x_2744_;
                    v_x_2735_ = v_r_2739_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2734_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1___boxed(
    mut v_init_2746_: *mut LeanObject,
    mut v_x_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_boxed_2748_: u64 = 0;
    let mut v_res_2749_: u64 = 0;
    let mut v_r_2750_: *mut LeanObject = core::ptr::null_mut();
    v_init_boxed_2748_ = lean_unbox_uint64(v_init_2746_);
    lean_dec_ref(v_init_2746_);
    v_res_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_2748_, v_x_2747_);
    lean_dec(v_x_2747_);
    v_r_2750_ = lean_box_uint64(v_res_2749_);
    return v_r_2750_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(
    mut v_as_2751_: *mut LeanObject,
    mut v_i_2752_: *mut LeanObject,
    mut v_stop_2753_: *mut LeanObject,
    mut v_b_2754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2755_: usize = 0;
    let mut v_stop_boxed_2756_: usize = 0;
    let mut v_b_boxed_2757_: u64 = 0;
    let mut v_res_2758_: u64 = 0;
    let mut v_r_2759_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2755_ = lean_unbox_usize(v_i_2752_);
    lean_dec(v_i_2752_);
    v_stop_boxed_2756_ = lean_unbox_usize(v_stop_2753_);
    lean_dec(v_stop_2753_);
    v_b_boxed_2757_ = lean_unbox_uint64(v_b_2754_);
    lean_dec_ref(v_b_2754_);
    v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_2751_, v_i_boxed_2755_, v_stop_boxed_2756_, v_b_boxed_2757_);
    lean_dec_ref(v_as_2751_);
    v_r_2759_ = lean_box_uint64(v_res_2758_);
    return v_r_2759_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(
    mut v_x_2760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2761_: u64 = 0;
    let mut v_r_2762_: *mut LeanObject = core::ptr::null_mut();
    v_res_2761_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_2760_);
    lean_dec(v_x_2760_);
    v_r_2762_ = lean_box_uint64(v_res_2761_);
    return v_r_2762_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(
    mut v_init_2763_: u64,
    mut v_t_2764_: *mut LeanObject,
) -> u64 {
    let mut v___x_2765_: u64 = 0;
    v___x_2765_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_2763_, v_t_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(
    mut v_init_2766_: *mut LeanObject,
    mut v_t_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_boxed_2768_: u64 = 0;
    let mut v_res_2769_: u64 = 0;
    let mut v_r_2770_: *mut LeanObject = core::ptr::null_mut();
    v_init_boxed_2768_ = lean_unbox_uint64(v_init_2766_);
    lean_dec_ref(v_init_2766_);
    v_res_2769_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_2768_, v_t_2767_);
    lean_dec(v_t_2767_);
    v_r_2770_ = lean_box_uint64(v_res_2769_);
    return v_r_2770_;
}
pub unsafe fn l_Lean_Json_instHashable___private__1(mut v_a_2771_: *mut LeanObject) -> u64 {
    let mut v___x_2772_: u64 = 0;
    v___x_2772_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_Json_instHashable___private__1___boxed(
    mut v_a_2773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2774_: u64 = 0;
    let mut v_r_2775_: *mut LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Lean_Json_instHashable___private__1(v_a_2773_);
    lean_dec(v_a_2773_);
    v_r_2775_ = lean_box_uint64(v_res_2774_);
    return v_r_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(
    mut v_k_2778_: *mut LeanObject,
    mut v_v_2779_: *mut LeanObject,
    mut v_t_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v_impl_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v_size_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_unused_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_unused_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_unused_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v_k_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v_unused_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut v_unused_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v_size_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_unused_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_unused_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v_k_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v_unused_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_unused_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2780_) == 0 {
                    v_size_2781_ = lean_ctor_get(v_t_2780_, 0);
                    v_k_2782_ = lean_ctor_get(v_t_2780_, 1);
                    v_v_2783_ = lean_ctor_get(v_t_2780_, 2);
                    v_l_2784_ = lean_ctor_get(v_t_2780_, 3);
                    v_r_2785_ = lean_ctor_get(v_t_2780_, 4);
                    v_isSharedCheck_3065_ = (!lean_is_exclusive(v_t_2780_)) as u8;
                    if v_isSharedCheck_3065_ == 0 {
                        v___x_2787_ = v_t_2780_;
                        v_isShared_2788_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_2785_);
                        lean_inc(v_l_2784_);
                        lean_inc(v_v_2783_);
                        lean_inc(v_k_2782_);
                        lean_inc(v_size_2781_);
                        lean_dec(v_t_2780_);
                        v___x_2787_ = lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3066_ = lean_unsigned_to_nat(1);
                    v___x_3067_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                    lean_ctor_set(v___x_3067_, 1, v_k_2778_);
                    lean_ctor_set(v___x_3067_, 2, v_v_2779_);
                    lean_ctor_set(v___x_3067_, 3, v_t_2780_);
                    lean_ctor_set(v___x_3067_, 4, v_t_2780_);
                    return v___x_3067_;
                }
            }
            1 => {
                v___x_2789_ = lean_string_compare(v_k_2778_, v_k_2782_);
                match v___x_2789_ {
                    0 => {
                        lean_dec(v_size_2781_);
                        v_impl_2790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_2778_, v_v_2779_, v_l_2784_);
                        v___x_2791_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_r_2785_) == 0 {
                            v_size_2792_ = lean_ctor_get(v_r_2785_, 0);
                            v_size_2793_ = lean_ctor_get(v_impl_2790_, 0);
                            lean_inc(v_size_2793_);
                            v_k_2794_ = lean_ctor_get(v_impl_2790_, 1);
                            lean_inc(v_k_2794_);
                            v_v_2795_ = lean_ctor_get(v_impl_2790_, 2);
                            lean_inc(v_v_2795_);
                            v_l_2796_ = lean_ctor_get(v_impl_2790_, 3);
                            lean_inc(v_l_2796_);
                            v_r_2797_ = lean_ctor_get(v_impl_2790_, 4);
                            lean_inc(v_r_2797_);
                            v___x_2798_ = lean_unsigned_to_nat(3);
                            v___x_2799_ = lean_nat_mul(v___x_2798_, v_size_2792_);
                            v___x_2800_ = lean_nat_dec_lt(v___x_2799_, v_size_2793_);
                            lean_dec(v___x_2799_);
                            if v___x_2800_ == 0 {
                                lean_dec(v_r_2797_);
                                lean_dec(v_l_2796_);
                                lean_dec(v_v_2795_);
                                lean_dec(v_k_2794_);
                                v___x_2801_ = lean_nat_add(v___x_2791_, v_size_2793_);
                                lean_dec(v_size_2793_);
                                v___x_2802_ = lean_nat_add(v___x_2801_, v_size_2792_);
                                lean_dec(v___x_2801_);
                                if v_isShared_2788_ == 0 {
                                    lean_ctor_set(v___x_2787_, 3, v_impl_2790_);
                                    lean_ctor_set(v___x_2787_, 0, v___x_2802_);
                                    v___x_2804_ = v___x_2787_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
                                    lean_ctor_set(v_reuseFailAlloc_2805_, 1, v_k_2782_);
                                    lean_ctor_set(v_reuseFailAlloc_2805_, 2, v_v_2783_);
                                    lean_ctor_set(v_reuseFailAlloc_2805_, 3, v_impl_2790_);
                                    lean_ctor_set(v_reuseFailAlloc_2805_, 4, v_r_2785_);
                                    v___x_2804_ = v_reuseFailAlloc_2805_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2871_ = (!lean_is_exclusive(v_impl_2790_)) as u8;
                                if v_isSharedCheck_2871_ == 0 {
                                    v_unused_2872_ = lean_ctor_get(v_impl_2790_, 4);
                                    lean_dec(v_unused_2872_);
                                    v_unused_2873_ = lean_ctor_get(v_impl_2790_, 3);
                                    lean_dec(v_unused_2873_);
                                    v_unused_2874_ = lean_ctor_get(v_impl_2790_, 2);
                                    lean_dec(v_unused_2874_);
                                    v_unused_2875_ = lean_ctor_get(v_impl_2790_, 1);
                                    lean_dec(v_unused_2875_);
                                    v_unused_2876_ = lean_ctor_get(v_impl_2790_, 0);
                                    lean_dec(v_unused_2876_);
                                    v___x_2807_ = v_impl_2790_;
                                    v_isShared_2808_ = v_isSharedCheck_2871_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2790_);
                                    v___x_2807_ = lean_box(0);
                                    v_isShared_2808_ = v_isSharedCheck_2871_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2877_ = lean_ctor_get(v_impl_2790_, 3);
                            lean_inc(v_l_2877_);
                            if lean_obj_tag(v_l_2877_) == 0 {
                                v_r_2878_ = lean_ctor_get(v_impl_2790_, 4);
                                v_k_2879_ = lean_ctor_get(v_impl_2790_, 1);
                                v_v_2880_ = lean_ctor_get(v_impl_2790_, 2);
                                v_isSharedCheck_2891_ = (!lean_is_exclusive(v_impl_2790_)) as u8;
                                if v_isSharedCheck_2891_ == 0 {
                                    v_unused_2892_ = lean_ctor_get(v_impl_2790_, 3);
                                    lean_dec(v_unused_2892_);
                                    v_unused_2893_ = lean_ctor_get(v_impl_2790_, 0);
                                    lean_dec(v_unused_2893_);
                                    v___x_2882_ = v_impl_2790_;
                                    v_isShared_2883_ = v_isSharedCheck_2891_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_2878_);
                                    lean_inc(v_v_2880_);
                                    lean_inc(v_k_2879_);
                                    lean_dec(v_impl_2790_);
                                    v___x_2882_ = lean_box(0);
                                    v_isShared_2883_ = v_isSharedCheck_2891_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2894_ = lean_ctor_get(v_impl_2790_, 4);
                                lean_inc(v_r_2894_);
                                if lean_obj_tag(v_r_2894_) == 0 {
                                    v_k_2895_ = lean_ctor_get(v_impl_2790_, 1);
                                    v_v_2896_ = lean_ctor_get(v_impl_2790_, 2);
                                    v_isSharedCheck_2919_ =
                                        (!lean_is_exclusive(v_impl_2790_)) as u8;
                                    if v_isSharedCheck_2919_ == 0 {
                                        v_unused_2920_ = lean_ctor_get(v_impl_2790_, 4);
                                        lean_dec(v_unused_2920_);
                                        v_unused_2921_ = lean_ctor_get(v_impl_2790_, 3);
                                        lean_dec(v_unused_2921_);
                                        v_unused_2922_ = lean_ctor_get(v_impl_2790_, 0);
                                        lean_dec(v_unused_2922_);
                                        v___x_2898_ = v_impl_2790_;
                                        v_isShared_2899_ = v_isSharedCheck_2919_;
                                        state = 16;
                                        continue;
                                    } else {
                                        lean_inc(v_v_2896_);
                                        lean_inc(v_k_2895_);
                                        lean_dec(v_impl_2790_);
                                        v___x_2898_ = lean_box(0);
                                        v_isShared_2899_ = v_isSharedCheck_2919_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2923_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2788_ == 0 {
                                        lean_ctor_set(v___x_2787_, 4, v_r_2894_);
                                        lean_ctor_set(v___x_2787_, 3, v_impl_2790_);
                                        lean_ctor_set(v___x_2787_, 0, v___x_2923_);
                                        v___x_2925_ = v___x_2787_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_2926_, 0, v___x_2923_);
                                        lean_ctor_set(v_reuseFailAlloc_2926_, 1, v_k_2782_);
                                        lean_ctor_set(v_reuseFailAlloc_2926_, 2, v_v_2783_);
                                        lean_ctor_set(v_reuseFailAlloc_2926_, 3, v_impl_2790_);
                                        lean_ctor_set(v_reuseFailAlloc_2926_, 4, v_r_2894_);
                                        v___x_2925_ = v_reuseFailAlloc_2926_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_2783_);
                        lean_dec(v_k_2782_);
                        if v_isShared_2788_ == 0 {
                            lean_ctor_set(v___x_2787_, 2, v_v_2779_);
                            lean_ctor_set(v___x_2787_, 1, v_k_2778_);
                            v___x_2928_ = v___x_2787_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_size_2781_);
                            lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2778_);
                            lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2779_);
                            lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_l_2784_);
                            lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2785_);
                            v___x_2928_ = v_reuseFailAlloc_2929_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_2781_);
                        v_impl_2930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_2778_, v_v_2779_, v_r_2785_);
                        v___x_2931_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_2784_) == 0 {
                            v_size_2932_ = lean_ctor_get(v_l_2784_, 0);
                            v_size_2933_ = lean_ctor_get(v_impl_2930_, 0);
                            lean_inc(v_size_2933_);
                            v_k_2934_ = lean_ctor_get(v_impl_2930_, 1);
                            lean_inc(v_k_2934_);
                            v_v_2935_ = lean_ctor_get(v_impl_2930_, 2);
                            lean_inc(v_v_2935_);
                            v_l_2936_ = lean_ctor_get(v_impl_2930_, 3);
                            lean_inc(v_l_2936_);
                            v_r_2937_ = lean_ctor_get(v_impl_2930_, 4);
                            lean_inc(v_r_2937_);
                            v___x_2938_ = lean_unsigned_to_nat(3);
                            v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
                            v___x_2940_ = lean_nat_dec_lt(v___x_2939_, v_size_2933_);
                            lean_dec(v___x_2939_);
                            if v___x_2940_ == 0 {
                                lean_dec(v_r_2937_);
                                lean_dec(v_l_2936_);
                                lean_dec(v_v_2935_);
                                lean_dec(v_k_2934_);
                                v___x_2941_ = lean_nat_add(v___x_2931_, v_size_2932_);
                                v___x_2942_ = lean_nat_add(v___x_2941_, v_size_2933_);
                                lean_dec(v_size_2933_);
                                lean_dec(v___x_2941_);
                                if v_isShared_2788_ == 0 {
                                    lean_ctor_set(v___x_2787_, 4, v_impl_2930_);
                                    lean_ctor_set(v___x_2787_, 0, v___x_2942_);
                                    v___x_2944_ = v___x_2787_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2945_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2945_, 0, v___x_2942_);
                                    lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_k_2782_);
                                    lean_ctor_set(v_reuseFailAlloc_2945_, 2, v_v_2783_);
                                    lean_ctor_set(v_reuseFailAlloc_2945_, 3, v_l_2784_);
                                    lean_ctor_set(v_reuseFailAlloc_2945_, 4, v_impl_2930_);
                                    v___x_2944_ = v_reuseFailAlloc_2945_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3009_ = (!lean_is_exclusive(v_impl_2930_)) as u8;
                                if v_isSharedCheck_3009_ == 0 {
                                    v_unused_3010_ = lean_ctor_get(v_impl_2930_, 4);
                                    lean_dec(v_unused_3010_);
                                    v_unused_3011_ = lean_ctor_get(v_impl_2930_, 3);
                                    lean_dec(v_unused_3011_);
                                    v_unused_3012_ = lean_ctor_get(v_impl_2930_, 2);
                                    lean_dec(v_unused_3012_);
                                    v_unused_3013_ = lean_ctor_get(v_impl_2930_, 1);
                                    lean_dec(v_unused_3013_);
                                    v_unused_3014_ = lean_ctor_get(v_impl_2930_, 0);
                                    lean_dec(v_unused_3014_);
                                    v___x_2947_ = v_impl_2930_;
                                    v_isShared_2948_ = v_isSharedCheck_3009_;
                                    state = 24;
                                    continue;
                                } else {
                                    lean_dec(v_impl_2930_);
                                    v___x_2947_ = lean_box(0);
                                    v_isShared_2948_ = v_isSharedCheck_3009_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3015_ = lean_ctor_get(v_impl_2930_, 3);
                            lean_inc(v_l_3015_);
                            if lean_obj_tag(v_l_3015_) == 0 {
                                v_r_3016_ = lean_ctor_get(v_impl_2930_, 4);
                                v_k_3017_ = lean_ctor_get(v_impl_2930_, 1);
                                v_v_3018_ = lean_ctor_get(v_impl_2930_, 2);
                                v_isSharedCheck_3041_ = (!lean_is_exclusive(v_impl_2930_)) as u8;
                                if v_isSharedCheck_3041_ == 0 {
                                    v_unused_3042_ = lean_ctor_get(v_impl_2930_, 3);
                                    lean_dec(v_unused_3042_);
                                    v_unused_3043_ = lean_ctor_get(v_impl_2930_, 0);
                                    lean_dec(v_unused_3043_);
                                    v___x_3020_ = v_impl_2930_;
                                    v_isShared_3021_ = v_isSharedCheck_3041_;
                                    state = 34;
                                    continue;
                                } else {
                                    lean_inc(v_r_3016_);
                                    lean_inc(v_v_3018_);
                                    lean_inc(v_k_3017_);
                                    lean_dec(v_impl_2930_);
                                    v___x_3020_ = lean_box(0);
                                    v_isShared_3021_ = v_isSharedCheck_3041_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3044_ = lean_ctor_get(v_impl_2930_, 4);
                                lean_inc(v_r_3044_);
                                if lean_obj_tag(v_r_3044_) == 0 {
                                    v_k_3045_ = lean_ctor_get(v_impl_2930_, 1);
                                    v_v_3046_ = lean_ctor_get(v_impl_2930_, 2);
                                    v_isSharedCheck_3057_ =
                                        (!lean_is_exclusive(v_impl_2930_)) as u8;
                                    if v_isSharedCheck_3057_ == 0 {
                                        v_unused_3058_ = lean_ctor_get(v_impl_2930_, 4);
                                        lean_dec(v_unused_3058_);
                                        v_unused_3059_ = lean_ctor_get(v_impl_2930_, 3);
                                        lean_dec(v_unused_3059_);
                                        v_unused_3060_ = lean_ctor_get(v_impl_2930_, 0);
                                        lean_dec(v_unused_3060_);
                                        v___x_3048_ = v_impl_2930_;
                                        v_isShared_3049_ = v_isSharedCheck_3057_;
                                        state = 39;
                                        continue;
                                    } else {
                                        lean_inc(v_v_3046_);
                                        lean_inc(v_k_3045_);
                                        lean_dec(v_impl_2930_);
                                        v___x_3048_ = lean_box(0);
                                        v_isShared_3049_ = v_isSharedCheck_3057_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3061_ = lean_unsigned_to_nat(2);
                                    if v_isShared_2788_ == 0 {
                                        lean_ctor_set(v___x_2787_, 4, v_impl_2930_);
                                        lean_ctor_set(v___x_2787_, 3, v_r_3044_);
                                        lean_ctor_set(v___x_2787_, 0, v___x_3061_);
                                        v___x_3063_ = v___x_2787_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
                                        lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_k_2782_);
                                        lean_ctor_set(v_reuseFailAlloc_3064_, 2, v_v_2783_);
                                        lean_ctor_set(v_reuseFailAlloc_3064_, 3, v_r_3044_);
                                        lean_ctor_set(v_reuseFailAlloc_3064_, 4, v_impl_2930_);
                                        v___x_3063_ = v_reuseFailAlloc_3064_;
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
                return v___x_2804_;
            }
            3 => {
                v_size_2809_ = lean_ctor_get(v_l_2796_, 0);
                v_size_2810_ = lean_ctor_get(v_r_2797_, 0);
                v_k_2811_ = lean_ctor_get(v_r_2797_, 1);
                v_v_2812_ = lean_ctor_get(v_r_2797_, 2);
                v_l_2813_ = lean_ctor_get(v_r_2797_, 3);
                v_r_2814_ = lean_ctor_get(v_r_2797_, 4);
                v___x_2815_ = lean_unsigned_to_nat(2);
                v___x_2816_ = lean_nat_mul(v___x_2815_, v_size_2809_);
                v___x_2817_ = lean_nat_dec_lt(v_size_2810_, v___x_2816_);
                lean_dec(v___x_2816_);
                if v___x_2817_ == 0 {
                    lean_inc(v_r_2814_);
                    lean_inc(v_l_2813_);
                    lean_inc(v_v_2812_);
                    lean_inc(v_k_2811_);
                    v_isSharedCheck_2846_ = (!lean_is_exclusive(v_r_2797_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v_unused_2847_ = lean_ctor_get(v_r_2797_, 4);
                        lean_dec(v_unused_2847_);
                        v_unused_2848_ = lean_ctor_get(v_r_2797_, 3);
                        lean_dec(v_unused_2848_);
                        v_unused_2849_ = lean_ctor_get(v_r_2797_, 2);
                        lean_dec(v_unused_2849_);
                        v_unused_2850_ = lean_ctor_get(v_r_2797_, 1);
                        lean_dec(v_unused_2850_);
                        v_unused_2851_ = lean_ctor_get(v_r_2797_, 0);
                        lean_dec(v_unused_2851_);
                        v___x_2819_ = v_r_2797_;
                        v_isShared_2820_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_r_2797_);
                        v___x_2819_ = lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2787_);
                    v___x_2852_ = lean_nat_add(v___x_2791_, v_size_2793_);
                    lean_dec(v_size_2793_);
                    v___x_2853_ = lean_nat_add(v___x_2852_, v_size_2792_);
                    lean_dec(v___x_2852_);
                    v___x_2854_ = lean_nat_add(v___x_2791_, v_size_2792_);
                    v___x_2855_ = lean_nat_add(v___x_2854_, v_size_2810_);
                    lean_dec(v___x_2854_);
                    lean_inc_ref(v_r_2785_);
                    if v_isShared_2808_ == 0 {
                        lean_ctor_set(v___x_2807_, 4, v_r_2785_);
                        lean_ctor_set(v___x_2807_, 3, v_r_2797_);
                        lean_ctor_set(v___x_2807_, 2, v_v_2783_);
                        lean_ctor_set(v___x_2807_, 1, v_k_2782_);
                        lean_ctor_set(v___x_2807_, 0, v___x_2855_);
                        v___x_2857_ = v___x_2807_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2855_);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2782_);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2783_);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_r_2797_);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_r_2785_);
                        v___x_2857_ = v_reuseFailAlloc_2870_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2821_ = lean_nat_add(v___x_2791_, v_size_2793_);
                lean_dec(v_size_2793_);
                v___x_2822_ = lean_nat_add(v___x_2821_, v_size_2792_);
                lean_dec(v___x_2821_);
                v___x_2834_ = lean_nat_add(v___x_2791_, v_size_2809_);
                if lean_obj_tag(v_l_2813_) == 0 {
                    v_size_2844_ = lean_ctor_get(v_l_2813_, 0);
                    lean_inc(v_size_2844_);
                    v___y_2836_ = v_size_2844_;
                    state = 8;
                    continue;
                } else {
                    v___x_2845_ = lean_unsigned_to_nat(0);
                    v___y_2836_ = v___x_2845_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2827_ = lean_nat_add(v___y_2825_, v___y_2826_);
                lean_dec(v___y_2826_);
                lean_dec(v___y_2825_);
                if v_isShared_2820_ == 0 {
                    lean_ctor_set(v___x_2819_, 4, v_r_2785_);
                    lean_ctor_set(v___x_2819_, 3, v_r_2814_);
                    lean_ctor_set(v___x_2819_, 2, v_v_2783_);
                    lean_ctor_set(v___x_2819_, 1, v_k_2782_);
                    lean_ctor_set(v___x_2819_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2827_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_r_2814_);
                    lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_r_2785_);
                    v___x_2829_ = v_reuseFailAlloc_2833_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2808_ == 0 {
                    lean_ctor_set(v___x_2807_, 4, v___x_2829_);
                    lean_ctor_set(v___x_2807_, 3, v___y_2824_);
                    lean_ctor_set(v___x_2807_, 2, v_v_2812_);
                    lean_ctor_set(v___x_2807_, 1, v_k_2811_);
                    lean_ctor_set(v___x_2807_, 0, v___x_2822_);
                    v___x_2831_ = v___x_2807_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2822_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2811_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2812_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___y_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 4, v___x_2829_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2831_;
            }
            8 => {
                v___x_2837_ = lean_nat_add(v___x_2834_, v___y_2836_);
                lean_dec(v___y_2836_);
                lean_dec(v___x_2834_);
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v_l_2813_);
                    lean_ctor_set(v___x_2787_, 3, v_l_2796_);
                    lean_ctor_set(v___x_2787_, 2, v_v_2795_);
                    lean_ctor_set(v___x_2787_, 1, v_k_2794_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2837_);
                    v___x_2839_ = v___x_2787_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2837_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_l_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_l_2813_);
                    v___x_2839_ = v_reuseFailAlloc_2843_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2840_ = lean_nat_add(v___x_2791_, v_size_2792_);
                if lean_obj_tag(v_r_2814_) == 0 {
                    v_size_2841_ = lean_ctor_get(v_r_2814_, 0);
                    lean_inc(v_size_2841_);
                    v___y_2824_ = v___x_2839_;
                    v___y_2825_ = v___x_2840_;
                    v___y_2826_ = v_size_2841_;
                    state = 5;
                    continue;
                } else {
                    v___x_2842_ = lean_unsigned_to_nat(0);
                    v___y_2824_ = v___x_2839_;
                    v___y_2825_ = v___x_2840_;
                    v___y_2826_ = v___x_2842_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2864_ = (!lean_is_exclusive(v_r_2785_)) as u8;
                if v_isSharedCheck_2864_ == 0 {
                    v_unused_2865_ = lean_ctor_get(v_r_2785_, 4);
                    lean_dec(v_unused_2865_);
                    v_unused_2866_ = lean_ctor_get(v_r_2785_, 3);
                    lean_dec(v_unused_2866_);
                    v_unused_2867_ = lean_ctor_get(v_r_2785_, 2);
                    lean_dec(v_unused_2867_);
                    v_unused_2868_ = lean_ctor_get(v_r_2785_, 1);
                    lean_dec(v_unused_2868_);
                    v_unused_2869_ = lean_ctor_get(v_r_2785_, 0);
                    lean_dec(v_unused_2869_);
                    v___x_2859_ = v_r_2785_;
                    v_isShared_2860_ = v_isSharedCheck_2864_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_2785_);
                    v___x_2859_ = lean_box(0);
                    v_isShared_2860_ = v_isSharedCheck_2864_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2860_ == 0 {
                    lean_ctor_set(v___x_2859_, 4, v___x_2857_);
                    lean_ctor_set(v___x_2859_, 3, v_l_2796_);
                    lean_ctor_set(v___x_2859_, 2, v_v_2795_);
                    lean_ctor_set(v___x_2859_, 1, v_k_2794_);
                    lean_ctor_set(v___x_2859_, 0, v___x_2853_);
                    v___x_2862_ = v___x_2859_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2853_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_k_2794_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_v_2795_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_l_2796_);
                    lean_ctor_set(v_reuseFailAlloc_2863_, 4, v___x_2857_);
                    v___x_2862_ = v_reuseFailAlloc_2863_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2862_;
            }
            13 => {
                v___x_2884_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_2878_);
                if v_isShared_2883_ == 0 {
                    lean_ctor_set(v___x_2882_, 3, v_r_2878_);
                    lean_ctor_set(v___x_2882_, 2, v_v_2783_);
                    lean_ctor_set(v___x_2882_, 1, v_k_2782_);
                    lean_ctor_set(v___x_2882_, 0, v___x_2791_);
                    v___x_2886_ = v___x_2882_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_r_2878_);
                    lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_r_2878_);
                    v___x_2886_ = v_reuseFailAlloc_2890_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v___x_2886_);
                    lean_ctor_set(v___x_2787_, 3, v_l_2877_);
                    lean_ctor_set(v___x_2787_, 2, v_v_2880_);
                    lean_ctor_set(v___x_2787_, 1, v_k_2879_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2884_);
                    v___x_2888_ = v___x_2787_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2884_);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2879_);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2880_);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_l_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2889_, 4, v___x_2886_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2888_;
            }
            16 => {
                v_k_2900_ = lean_ctor_get(v_r_2894_, 1);
                v_v_2901_ = lean_ctor_get(v_r_2894_, 2);
                v_isSharedCheck_2915_ = (!lean_is_exclusive(v_r_2894_)) as u8;
                if v_isSharedCheck_2915_ == 0 {
                    v_unused_2916_ = lean_ctor_get(v_r_2894_, 4);
                    lean_dec(v_unused_2916_);
                    v_unused_2917_ = lean_ctor_get(v_r_2894_, 3);
                    lean_dec(v_unused_2917_);
                    v_unused_2918_ = lean_ctor_get(v_r_2894_, 0);
                    lean_dec(v_unused_2918_);
                    v___x_2903_ = v_r_2894_;
                    v_isShared_2904_ = v_isSharedCheck_2915_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_v_2901_);
                    lean_inc(v_k_2900_);
                    lean_dec(v_r_2894_);
                    v___x_2903_ = lean_box(0);
                    v_isShared_2904_ = v_isSharedCheck_2915_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2905_ = lean_unsigned_to_nat(3);
                if v_isShared_2904_ == 0 {
                    lean_ctor_set(v___x_2903_, 4, v_l_2877_);
                    lean_ctor_set(v___x_2903_, 3, v_l_2877_);
                    lean_ctor_set(v___x_2903_, 2, v_v_2896_);
                    lean_ctor_set(v___x_2903_, 1, v_k_2895_);
                    lean_ctor_set(v___x_2903_, 0, v___x_2791_);
                    v___x_2907_ = v___x_2903_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_k_2895_);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_v_2896_);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_l_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_l_2877_);
                    v___x_2907_ = v_reuseFailAlloc_2914_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2899_ == 0 {
                    lean_ctor_set(v___x_2898_, 4, v_l_2877_);
                    lean_ctor_set(v___x_2898_, 2, v_v_2783_);
                    lean_ctor_set(v___x_2898_, 1, v_k_2782_);
                    lean_ctor_set(v___x_2898_, 0, v___x_2791_);
                    v___x_2909_ = v___x_2898_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2791_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_l_2877_);
                    lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_l_2877_);
                    v___x_2909_ = v_reuseFailAlloc_2913_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v___x_2909_);
                    lean_ctor_set(v___x_2787_, 3, v___x_2907_);
                    lean_ctor_set(v___x_2787_, 2, v_v_2901_);
                    lean_ctor_set(v___x_2787_, 1, v_k_2900_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2905_);
                    v___x_2911_ = v___x_2787_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2900_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2901_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 3, v___x_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2909_);
                    v___x_2911_ = v_reuseFailAlloc_2912_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2911_;
            }
            21 => {
                return v___x_2925_;
            }
            22 => {
                return v___x_2928_;
            }
            23 => {
                return v___x_2944_;
            }
            24 => {
                v_size_2949_ = lean_ctor_get(v_l_2936_, 0);
                v_k_2950_ = lean_ctor_get(v_l_2936_, 1);
                v_v_2951_ = lean_ctor_get(v_l_2936_, 2);
                v_l_2952_ = lean_ctor_get(v_l_2936_, 3);
                v_r_2953_ = lean_ctor_get(v_l_2936_, 4);
                v_size_2954_ = lean_ctor_get(v_r_2937_, 0);
                v___x_2955_ = lean_unsigned_to_nat(2);
                v___x_2956_ = lean_nat_mul(v___x_2955_, v_size_2954_);
                v___x_2957_ = lean_nat_dec_lt(v_size_2949_, v___x_2956_);
                lean_dec(v___x_2956_);
                if v___x_2957_ == 0 {
                    lean_inc(v_r_2953_);
                    lean_inc(v_l_2952_);
                    lean_inc(v_v_2951_);
                    lean_inc(v_k_2950_);
                    v_isSharedCheck_2985_ = (!lean_is_exclusive(v_l_2936_)) as u8;
                    if v_isSharedCheck_2985_ == 0 {
                        v_unused_2986_ = lean_ctor_get(v_l_2936_, 4);
                        lean_dec(v_unused_2986_);
                        v_unused_2987_ = lean_ctor_get(v_l_2936_, 3);
                        lean_dec(v_unused_2987_);
                        v_unused_2988_ = lean_ctor_get(v_l_2936_, 2);
                        lean_dec(v_unused_2988_);
                        v_unused_2989_ = lean_ctor_get(v_l_2936_, 1);
                        lean_dec(v_unused_2989_);
                        v_unused_2990_ = lean_ctor_get(v_l_2936_, 0);
                        lean_dec(v_unused_2990_);
                        v___x_2959_ = v_l_2936_;
                        v_isShared_2960_ = v_isSharedCheck_2985_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_l_2936_);
                        v___x_2959_ = lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2985_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2787_);
                    v___x_2991_ = lean_nat_add(v___x_2931_, v_size_2932_);
                    v___x_2992_ = lean_nat_add(v___x_2991_, v_size_2933_);
                    lean_dec(v_size_2933_);
                    v___x_2993_ = lean_nat_add(v___x_2991_, v_size_2949_);
                    lean_dec(v___x_2991_);
                    lean_inc_ref(v_l_2784_);
                    if v_isShared_2948_ == 0 {
                        lean_ctor_set(v___x_2947_, 4, v_l_2936_);
                        lean_ctor_set(v___x_2947_, 3, v_l_2784_);
                        lean_ctor_set(v___x_2947_, 2, v_v_2783_);
                        lean_ctor_set(v___x_2947_, 1, v_k_2782_);
                        lean_ctor_set(v___x_2947_, 0, v___x_2993_);
                        v___x_2995_ = v___x_2947_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2993_);
                        lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_k_2782_);
                        lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_v_2783_);
                        lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_l_2784_);
                        lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_l_2936_);
                        v___x_2995_ = v_reuseFailAlloc_3008_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2961_ = lean_nat_add(v___x_2931_, v_size_2932_);
                v___x_2962_ = lean_nat_add(v___x_2961_, v_size_2933_);
                lean_dec(v_size_2933_);
                if lean_obj_tag(v_l_2952_) == 0 {
                    v_size_2983_ = lean_ctor_get(v_l_2952_, 0);
                    lean_inc(v_size_2983_);
                    v___y_2975_ = v_size_2983_;
                    state = 29;
                    continue;
                } else {
                    v___x_2984_ = lean_unsigned_to_nat(0);
                    v___y_2975_ = v___x_2984_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2967_ = lean_nat_add(v___y_2965_, v___y_2966_);
                lean_dec(v___y_2966_);
                lean_dec(v___y_2965_);
                if v_isShared_2960_ == 0 {
                    lean_ctor_set(v___x_2959_, 4, v_r_2937_);
                    lean_ctor_set(v___x_2959_, 3, v_r_2953_);
                    lean_ctor_set(v___x_2959_, 2, v_v_2935_);
                    lean_ctor_set(v___x_2959_, 1, v_k_2934_);
                    lean_ctor_set(v___x_2959_, 0, v___x_2967_);
                    v___x_2969_ = v___x_2959_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2967_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_k_2934_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_v_2935_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_r_2953_);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 4, v_r_2937_);
                    v___x_2969_ = v_reuseFailAlloc_2973_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2948_ == 0 {
                    lean_ctor_set(v___x_2947_, 4, v___x_2969_);
                    lean_ctor_set(v___x_2947_, 3, v___y_2964_);
                    lean_ctor_set(v___x_2947_, 2, v_v_2951_);
                    lean_ctor_set(v___x_2947_, 1, v_k_2950_);
                    lean_ctor_set(v___x_2947_, 0, v___x_2962_);
                    v___x_2971_ = v___x_2947_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2962_);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_k_2950_);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_v_2951_);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 3, v___y_2964_);
                    lean_ctor_set(v_reuseFailAlloc_2972_, 4, v___x_2969_);
                    v___x_2971_ = v_reuseFailAlloc_2972_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2971_;
            }
            29 => {
                v___x_2976_ = lean_nat_add(v___x_2961_, v___y_2975_);
                lean_dec(v___y_2975_);
                lean_dec(v___x_2961_);
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v_l_2952_);
                    lean_ctor_set(v___x_2787_, 0, v___x_2976_);
                    v___x_2978_ = v___x_2787_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2976_);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_l_2784_);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_l_2952_);
                    v___x_2978_ = v_reuseFailAlloc_2982_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2979_ = lean_nat_add(v___x_2931_, v_size_2954_);
                if lean_obj_tag(v_r_2953_) == 0 {
                    v_size_2980_ = lean_ctor_get(v_r_2953_, 0);
                    lean_inc(v_size_2980_);
                    v___y_2964_ = v___x_2978_;
                    v___y_2965_ = v___x_2979_;
                    v___y_2966_ = v_size_2980_;
                    state = 26;
                    continue;
                } else {
                    v___x_2981_ = lean_unsigned_to_nat(0);
                    v___y_2964_ = v___x_2978_;
                    v___y_2965_ = v___x_2979_;
                    v___y_2966_ = v___x_2981_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3002_ = (!lean_is_exclusive(v_l_2784_)) as u8;
                if v_isSharedCheck_3002_ == 0 {
                    v_unused_3003_ = lean_ctor_get(v_l_2784_, 4);
                    lean_dec(v_unused_3003_);
                    v_unused_3004_ = lean_ctor_get(v_l_2784_, 3);
                    lean_dec(v_unused_3004_);
                    v_unused_3005_ = lean_ctor_get(v_l_2784_, 2);
                    lean_dec(v_unused_3005_);
                    v_unused_3006_ = lean_ctor_get(v_l_2784_, 1);
                    lean_dec(v_unused_3006_);
                    v_unused_3007_ = lean_ctor_get(v_l_2784_, 0);
                    lean_dec(v_unused_3007_);
                    v___x_2997_ = v_l_2784_;
                    v_isShared_2998_ = v_isSharedCheck_3002_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_l_2784_);
                    v___x_2997_ = lean_box(0);
                    v_isShared_2998_ = v_isSharedCheck_3002_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2998_ == 0 {
                    lean_ctor_set(v___x_2997_, 4, v_r_2937_);
                    lean_ctor_set(v___x_2997_, 3, v___x_2995_);
                    lean_ctor_set(v___x_2997_, 2, v_v_2935_);
                    lean_ctor_set(v___x_2997_, 1, v_k_2934_);
                    lean_ctor_set(v___x_2997_, 0, v___x_2992_);
                    v___x_3000_ = v___x_2997_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2992_);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_k_2934_);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_v_2935_);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 3, v___x_2995_);
                    lean_ctor_set(v_reuseFailAlloc_3001_, 4, v_r_2937_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3000_;
            }
            34 => {
                v_k_3022_ = lean_ctor_get(v_l_3015_, 1);
                v_v_3023_ = lean_ctor_get(v_l_3015_, 2);
                v_isSharedCheck_3037_ = (!lean_is_exclusive(v_l_3015_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v_unused_3038_ = lean_ctor_get(v_l_3015_, 4);
                    lean_dec(v_unused_3038_);
                    v_unused_3039_ = lean_ctor_get(v_l_3015_, 3);
                    lean_dec(v_unused_3039_);
                    v_unused_3040_ = lean_ctor_get(v_l_3015_, 0);
                    lean_dec(v_unused_3040_);
                    v___x_3025_ = v_l_3015_;
                    v_isShared_3026_ = v_isSharedCheck_3037_;
                    state = 35;
                    continue;
                } else {
                    lean_inc(v_v_3023_);
                    lean_inc(v_k_3022_);
                    lean_dec(v_l_3015_);
                    v___x_3025_ = lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3037_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3027_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_3016_, 2);
                if v_isShared_3026_ == 0 {
                    lean_ctor_set(v___x_3025_, 4, v_r_3016_);
                    lean_ctor_set(v___x_3025_, 3, v_r_3016_);
                    lean_ctor_set(v___x_3025_, 2, v_v_2783_);
                    lean_ctor_set(v___x_3025_, 1, v_k_2782_);
                    lean_ctor_set(v___x_3025_, 0, v___x_2931_);
                    v___x_3029_ = v___x_3025_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2931_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_r_3016_);
                    lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_r_3016_);
                    v___x_3029_ = v_reuseFailAlloc_3036_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                lean_inc(v_r_3016_);
                if v_isShared_3021_ == 0 {
                    lean_ctor_set(v___x_3020_, 3, v_r_3016_);
                    lean_ctor_set(v___x_3020_, 0, v___x_2931_);
                    v___x_3031_ = v___x_3020_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_2931_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3017_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3018_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 3, v_r_3016_);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 4, v_r_3016_);
                    v___x_3031_ = v_reuseFailAlloc_3035_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v___x_3031_);
                    lean_ctor_set(v___x_2787_, 3, v___x_3029_);
                    lean_ctor_set(v___x_2787_, 2, v_v_3023_);
                    lean_ctor_set(v___x_2787_, 1, v_k_3022_);
                    lean_ctor_set(v___x_2787_, 0, v___x_3027_);
                    v___x_3033_ = v___x_2787_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3027_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_k_3022_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_v_3023_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 3, v___x_3029_);
                    lean_ctor_set(v_reuseFailAlloc_3034_, 4, v___x_3031_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3033_;
            }
            39 => {
                v___x_3050_ = lean_unsigned_to_nat(3);
                if v_isShared_3049_ == 0 {
                    lean_ctor_set(v___x_3048_, 4, v_l_3015_);
                    lean_ctor_set(v___x_3048_, 2, v_v_2783_);
                    lean_ctor_set(v___x_3048_, 1, v_k_2782_);
                    lean_ctor_set(v___x_3048_, 0, v___x_2931_);
                    v___x_3052_ = v___x_3048_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_2931_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_k_2782_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_v_2783_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_l_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_l_3015_);
                    v___x_3052_ = v_reuseFailAlloc_3056_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2788_ == 0 {
                    lean_ctor_set(v___x_2787_, 4, v_r_3044_);
                    lean_ctor_set(v___x_2787_, 3, v___x_3052_);
                    lean_ctor_set(v___x_2787_, 2, v_v_3046_);
                    lean_ctor_set(v___x_2787_, 1, v_k_3045_);
                    lean_ctor_set(v___x_2787_, 0, v___x_3050_);
                    v___x_3054_ = v___x_2787_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3050_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_3045_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_3046_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 3, v___x_3052_);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_r_3044_);
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3054_;
            }
            42 => {
                return v___x_3063_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(
    mut v_as_x27_3068_: *mut LeanObject,
    mut v_b_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_3068_) == 0 {
                    return v_b_3069_;
                } else {
                    v_head_3070_ = lean_ctor_get(v_as_x27_3068_, 0);
                    v_tail_3071_ = lean_ctor_get(v_as_x27_3068_, 1);
                    v_fst_3072_ = lean_ctor_get(v_head_3070_, 0);
                    v_snd_3073_ = lean_ctor_get(v_head_3070_, 1);
                    lean_inc(v_snd_3073_);
                    lean_inc(v_fst_3072_);
                    v_r_3074_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_fst_3072_, v_snd_3073_, v_b_3069_);
                    v_as_x27_3068_ = v_tail_3071_;
                    v_b_3069_ = v_r_3074_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg___boxed(
    mut v_as_x27_3076_: *mut LeanObject,
    mut v_b_3077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3078_: *mut LeanObject = core::ptr::null_mut();
    v_res_3078_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_3076_, v_b_3077_);
    lean_dec(v_as_x27_3076_);
    return v_res_3078_;
}
pub unsafe fn l_Lean_Json_mkObj(mut v_o_3079_: *mut LeanObject) -> *mut LeanObject {
    let mut v_r_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    v_r_3080_ = lean_box(1);
    v___x_3081_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_3079_, v_r_3080_);
    v___x_3082_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_3082_, 0, v___x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_Json_mkObj___boxed(mut v_o_3083_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3084_: *mut LeanObject = core::ptr::null_mut();
    v_res_3084_ = l_Lean_Json_mkObj(v_o_3083_);
    lean_dec(v_o_3083_);
    return v_res_3084_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(
    mut v_00_u03b2_3085_: *mut LeanObject,
    mut v_k_3086_: *mut LeanObject,
    mut v_v_3087_: *mut LeanObject,
    mut v_t_3088_: *mut LeanObject,
    mut v_hl_3089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(
        v_k_3086_, v_v_3087_, v_t_3088_,
    );
    return v___x_3090_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(
    mut v_as_3091_: *mut LeanObject,
    mut v_as_x27_3092_: *mut LeanObject,
    mut v_b_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    v___x_3095_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_3092_, v_b_3093_);
    return v___x_3095_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(
    mut v_as_3096_: *mut LeanObject,
    mut v_as_x27_3097_: *mut LeanObject,
    mut v_b_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3100_: *mut LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(
        v_as_3096_,
        v_as_x27_3097_,
        v_b_3098_,
        v_a_3099_,
    );
    lean_dec(v_as_x27_3097_);
    lean_dec(v_as_3096_);
    return v_res_3100_;
}
pub unsafe fn l_Lean_Json_instCoeNat___lam__0(mut v_n_3101_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Lean_JsonNumber_fromNat(v_n_3101_);
    v___x_3103_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_3103_, 0, v___x_3102_);
    return v___x_3103_;
}
pub unsafe fn l_Lean_Json_instCoeInt___lam__0(mut v_n_3106_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3107_ = l_Lean_JsonNumber_fromInt(v_n_3106_);
    v___x_3108_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_3108_, 0, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_Json_instCoeString___lam__0(
    mut v_s_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v___x_3112_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_3112_, 0, v_s_3111_);
    return v___x_3112_;
}
pub unsafe fn l_Lean_Json_instCoeBool___lam__0(mut v_b_3115_: u8) -> *mut LeanObject {
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    v___x_3116_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_3116_, 0 as u32, v_b_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Lean_Json_instCoeBool___lam__0___boxed(
    mut v_b_3117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_3118_: u8 = 0;
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_3118_ = (lean_unbox(v_b_3117_) as u8);
    v_res_3119_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_3118_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_Json_instOfNat(mut v_n_3122_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_JsonNumber_fromNat(v_n_3122_);
    v___x_3124_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_3124_, 0, v___x_3123_);
    return v___x_3124_;
}
pub unsafe fn l_Lean_Json_isNull(mut v_x_3125_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_3125_) == 0 {
        let mut v___x_3126_: u8 = 0;
        v___x_3126_ = 1;
        return v___x_3126_;
    } else {
        let mut v___x_3127_: u8 = 0;
        v___x_3127_ = 0;
        return v___x_3127_;
    }
}
pub unsafe fn l_Lean_Json_isNull___boxed(mut v_x_3128_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3129_: u8 = 0;
    let mut v_r_3130_: *mut LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_Lean_Json_isNull(v_x_3128_);
    lean_dec(v_x_3128_);
    v_r_3130_ = lean_box((v_res_3129_) as usize);
    return v_r_3130_;
}
pub unsafe fn l_Lean_Json_getObj_x3f(mut v_x_3134_: *mut LeanObject) -> *mut LeanObject {
    let mut v_kvPairs_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3134_) == 5 {
                    v_kvPairs_3135_ = lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3142_ = (!lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3142_ == 0 {
                        v___x_3137_ = v_x_3134_;
                        v_isShared_3138_ = v_isSharedCheck_3142_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_kvPairs_3135_);
                        lean_dec(v_x_3134_);
                        v___x_3137_ = lean_box(0);
                        v_isShared_3138_ = v_isSharedCheck_3142_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3134_);
                    v___x_3143_ = l_Lean_Json_getObj_x3f___closed__1;
                    return v___x_3143_;
                }
            }
            1 => {
                if v_isShared_3138_ == 0 {
                    lean_ctor_set_tag(v___x_3137_, 1);
                    v___x_3140_ = v___x_3137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_kvPairs_3135_);
                    v___x_3140_ = v_reuseFailAlloc_3141_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getArr_x3f(mut v_x_3147_: *mut LeanObject) -> *mut LeanObject {
    let mut v_elems_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3147_) == 4 {
                    v_elems_3148_ = lean_ctor_get(v_x_3147_, 0);
                    v_isSharedCheck_3155_ = (!lean_is_exclusive(v_x_3147_)) as u8;
                    if v_isSharedCheck_3155_ == 0 {
                        v___x_3150_ = v_x_3147_;
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_elems_3148_);
                        lean_dec(v_x_3147_);
                        v___x_3150_ = lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3147_);
                    v___x_3156_ = l_Lean_Json_getArr_x3f___closed__1;
                    return v___x_3156_;
                }
            }
            1 => {
                if v_isShared_3151_ == 0 {
                    lean_ctor_set_tag(v___x_3150_, 1);
                    v___x_3153_ = v___x_3150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_elems_3148_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getStr_x3f(mut v_x_3160_: *mut LeanObject) -> *mut LeanObject {
    let mut v_s_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3160_) == 3 {
                    v_s_3161_ = lean_ctor_get(v_x_3160_, 0);
                    v_isSharedCheck_3168_ = (!lean_is_exclusive(v_x_3160_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3163_ = v_x_3160_;
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_3161_);
                        lean_dec(v_x_3160_);
                        v___x_3163_ = lean_box(0);
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3160_);
                    v___x_3169_ = l_Lean_Json_getStr_x3f___closed__1;
                    return v___x_3169_;
                }
            }
            1 => {
                if v_isShared_3164_ == 0 {
                    lean_ctor_set_tag(v___x_3163_, 1);
                    v___x_3166_ = v___x_3163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_s_3161_);
                    v___x_3166_ = v_reuseFailAlloc_3167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getNat_x3f(mut v_x_3173_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3179_: u8 = 0;
    let mut v_mantissa_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_3184_: u8 = 0;
    let mut v___x_3185_: u8 = 0;
    let mut v_a_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3173_) == 2 {
                    v_n_3176_ = lean_ctor_get(v_x_3173_, 0);
                    v_isSharedCheck_3190_ = (!lean_is_exclusive(v_x_3173_)) as u8;
                    if v_isSharedCheck_3190_ == 0 {
                        v___x_3178_ = v_x_3173_;
                        v_isShared_3179_ = v_isSharedCheck_3190_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_n_3176_);
                        lean_dec(v_x_3173_);
                        v___x_3178_ = lean_box(0);
                        v_isShared_3179_ = v_isSharedCheck_3190_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3173_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3175_ = l_Lean_Json_getNat_x3f___closed__1;
                return v___x_3175_;
            }
            2 => {
                v_mantissa_3180_ = lean_ctor_get(v_n_3176_, 0);
                lean_inc(v_mantissa_3180_);
                v_exponent_3181_ = lean_ctor_get(v_n_3176_, 1);
                lean_inc(v_exponent_3181_);
                lean_dec_ref(v_n_3176_);
                v_natZero_3182_ = lean_unsigned_to_nat(0);
                v_intZero_3183_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v_isNeg_3184_ = lean_int_dec_lt(v_mantissa_3180_, v_intZero_3183_);
                if v_isNeg_3184_ == 0 {
                    v___x_3185_ = lean_nat_dec_eq(v_exponent_3181_, v_natZero_3182_);
                    lean_dec(v_exponent_3181_);
                    if v___x_3185_ == 0 {
                        lean_dec(v_mantissa_3180_);
                        lean_del_object(v___x_3178_);
                        state = 1;
                        continue;
                    } else {
                        v_a_3186_ = lean_nat_abs(v_mantissa_3180_);
                        lean_dec(v_mantissa_3180_);
                        if v_isShared_3179_ == 0 {
                            lean_ctor_set_tag(v___x_3178_, 1);
                            lean_ctor_set(v___x_3178_, 0, v_a_3186_);
                            v___x_3188_ = v___x_3178_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3189_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3186_);
                            v___x_3188_ = v_reuseFailAlloc_3189_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_exponent_3181_);
                    lean_dec(v_mantissa_3180_);
                    lean_del_object(v___x_3178_);
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_3188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getInt_x3f(mut v_x_3194_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v_mantissa_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exponent_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3194_) == 2 {
                    v_n_3197_ = lean_ctor_get(v_x_3194_, 0);
                    v_isSharedCheck_3208_ = (!lean_is_exclusive(v_x_3194_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3199_ = v_x_3194_;
                        v_isShared_3200_ = v_isSharedCheck_3208_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_n_3197_);
                        lean_dec(v_x_3194_);
                        v___x_3199_ = lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3208_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3194_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3196_ = l_Lean_Json_getInt_x3f___closed__1;
                return v___x_3196_;
            }
            2 => {
                v_mantissa_3201_ = lean_ctor_get(v_n_3197_, 0);
                lean_inc(v_mantissa_3201_);
                v_exponent_3202_ = lean_ctor_get(v_n_3197_, 1);
                lean_inc(v_exponent_3202_);
                lean_dec_ref(v_n_3197_);
                v___x_3203_ = lean_unsigned_to_nat(0);
                v___x_3204_ = lean_nat_dec_eq(v_exponent_3202_, v___x_3203_);
                lean_dec(v_exponent_3202_);
                if v___x_3204_ == 0 {
                    lean_dec(v_mantissa_3201_);
                    lean_del_object(v___x_3199_);
                    state = 1;
                    continue;
                } else {
                    if v_isShared_3200_ == 0 {
                        lean_ctor_set_tag(v___x_3199_, 1);
                        lean_ctor_set(v___x_3199_, 0, v_mantissa_3201_);
                        v___x_3206_ = v___x_3199_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_mantissa_3201_);
                        v___x_3206_ = v_reuseFailAlloc_3207_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getBool_x3f(mut v_x_3212_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3212_) == 1 {
        let mut v_b_3213_: u8 = 0;
        let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
        v_b_3213_ = lean_ctor_get_uint8(v_x_3212_, 0 as u32);
        v___x_3214_ = lean_box((v_b_3213_) as usize);
        v___x_3215_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3215_, 0, v___x_3214_);
        return v___x_3215_;
    } else {
        let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
        v___x_3216_ = l_Lean_Json_getBool_x3f___closed__1;
        return v___x_3216_;
    }
}
pub unsafe fn l_Lean_Json_getBool_x3f___boxed(mut v_x_3217_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_3218_: *mut LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Lean_Json_getBool_x3f(v_x_3217_);
    lean_dec(v_x_3217_);
    return v_res_3218_;
}
pub unsafe fn l_Lean_Json_getNum_x3f(mut v_x_3222_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3222_) == 2 {
                    v_n_3223_ = lean_ctor_get(v_x_3222_, 0);
                    v_isSharedCheck_3230_ = (!lean_is_exclusive(v_x_3222_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v___x_3225_ = v_x_3222_;
                        v_isShared_3226_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_n_3223_);
                        lean_dec(v_x_3222_);
                        v___x_3225_ = lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3222_);
                    v___x_3231_ = l_Lean_Json_getNum_x3f___closed__1;
                    return v___x_3231_;
                }
            }
            1 => {
                if v_isShared_3226_ == 0 {
                    lean_ctor_set_tag(v___x_3225_, 1);
                    v___x_3228_ = v___x_3225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_n_3223_);
                    v___x_3228_ = v_reuseFailAlloc_3229_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3228_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjVal_x3f(
    mut v_x_3235_: *mut LeanObject,
    mut v_x_3236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kvPairs_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3235_) == 5 {
                    v_kvPairs_3237_ = lean_ctor_get(v_x_3235_, 0);
                    v_isSharedCheck_3255_ = (!lean_is_exclusive(v_x_3235_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3239_ = v_x_3235_;
                        v_isShared_3240_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_kvPairs_3237_);
                        lean_dec(v_x_3235_);
                        v___x_3239_ = lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3235_);
                    v___x_3256_ = l_Lean_Json_getObjVal_x3f___closed__1;
                    return v___x_3256_;
                }
            }
            1 => {
                v___x_3241_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_3237_, v_x_3236_);
                lean_dec(v_kvPairs_3237_);
                if lean_obj_tag(v___x_3241_) == 0 {
                    v___x_3242_ = l_Lean_Json_getObjVal_x3f___closed__0;
                    v___x_3243_ = lean_string_append(v___x_3242_, v_x_3236_);
                    if v_isShared_3240_ == 0 {
                        lean_ctor_set_tag(v___x_3239_, 0);
                        lean_ctor_set(v___x_3239_, 0, v___x_3243_);
                        v___x_3245_ = v___x_3239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                        v___x_3245_ = v_reuseFailAlloc_3246_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3239_);
                    v_val_3247_ = lean_ctor_get(v___x_3241_, 0);
                    v_isSharedCheck_3254_ = (!lean_is_exclusive(v___x_3241_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3249_ = v___x_3241_;
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_3247_);
                        lean_dec(v___x_3241_);
                        v___x_3249_ = lean_box(0);
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3245_;
            }
            3 => {
                if v_isShared_3250_ == 0 {
                    v___x_3252_ = v___x_3249_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3247_);
                    v___x_3252_ = v_reuseFailAlloc_3253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjVal_x3f___boxed(
    mut v_x_3257_: *mut LeanObject,
    mut v_x_3258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3259_: *mut LeanObject = core::ptr::null_mut();
    v_res_3259_ = l_Lean_Json_getObjVal_x3f(v_x_3257_, v_x_3258_);
    lean_dec_ref(v_x_3258_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Json_getArrVal_x3f(
    mut v_x_3263_: *mut LeanObject,
    mut v_x_3264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_elems_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3263_) == 4 {
                    v_elems_3265_ = lean_ctor_get(v_x_3263_, 0);
                    v_isSharedCheck_3281_ = (!lean_is_exclusive(v_x_3263_)) as u8;
                    if v_isSharedCheck_3281_ == 0 {
                        v___x_3267_ = v_x_3263_;
                        v_isShared_3268_ = v_isSharedCheck_3281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_elems_3265_);
                        lean_dec(v_x_3263_);
                        v___x_3267_ = lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3281_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3264_);
                    lean_dec(v_x_3263_);
                    v___x_3282_ = l_Lean_Json_getArrVal_x3f___closed__1;
                    return v___x_3282_;
                }
            }
            1 => {
                v___x_3269_ = lean_array_get_size(v_elems_3265_);
                v___x_3270_ = lean_nat_dec_lt(v_x_3264_, v___x_3269_);
                if v___x_3270_ == 0 {
                    lean_dec_ref(v_elems_3265_);
                    v___x_3271_ = l_Lean_Json_getArrVal_x3f___closed__0;
                    v___x_3272_ = l_Nat_reprFast(v_x_3264_);
                    v___x_3273_ = lean_string_append(v___x_3271_, v___x_3272_);
                    lean_dec_ref(v___x_3272_);
                    if v_isShared_3268_ == 0 {
                        lean_ctor_set_tag(v___x_3267_, 0);
                        lean_ctor_set(v___x_3267_, 0, v___x_3273_);
                        v___x_3275_ = v___x_3267_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3276_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
                        v___x_3275_ = v_reuseFailAlloc_3276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3277_ = lean_array_fget(v_elems_3265_, v_x_3264_);
                    lean_dec(v_x_3264_);
                    lean_dec_ref(v_elems_3265_);
                    if v_isShared_3268_ == 0 {
                        lean_ctor_set_tag(v___x_3267_, 1);
                        lean_ctor_set(v___x_3267_, 0, v___x_3277_);
                        v___x_3279_ = v___x_3267_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
                        v___x_3279_ = v_reuseFailAlloc_3280_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3275_;
            }
            3 => {
                return v___x_3279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValD(
    mut v_j_3283_: *mut LeanObject,
    mut v_k_3284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_Json_getObjVal_x3f(v_j_3283_, v_k_3284_);
    if lean_obj_tag(v___x_3285_) == 0 {
        let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3285_, 1);
        v___x_3286_ = lean_box(0);
        return v___x_3286_;
    } else {
        let mut v_a_3287_: *mut LeanObject = core::ptr::null_mut();
        v_a_3287_ = lean_ctor_get(v___x_3285_, 0);
        lean_inc(v_a_3287_);
        lean_dec_ref_known(v___x_3285_, 1);
        return v_a_3287_;
    }
}
pub unsafe fn l_Lean_Json_getObjValD___boxed(
    mut v_j_3288_: *mut LeanObject,
    mut v_k_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3290_: *mut LeanObject = core::ptr::null_mut();
    v_res_3290_ = l_Lean_Json_getObjValD(v_j_3288_, v_k_3289_);
    lean_dec_ref(v_k_3289_);
    return v_res_3290_;
}
pub unsafe fn l_panic___at___00Lean_Json_setObjVal_x21_spec__1(
    mut v_msg_3291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    v___x_3292_ = lean_box(0);
    v___x_3293_ = lean_panic_fn_borrowed(v___x_3292_, v_msg_3291_);
    return v___x_3293_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(
    mut v_msg_3294_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    v___x_3295_ = lean_box(1);
    v___x_3296_ = lean_panic_fn_borrowed(v___x_3295_, v_msg_3294_);
    return v___x_3296_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    v___x_3300_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2;
    v___x_3301_ = lean_unsigned_to_nat(35);
    v___x_3302_ = lean_unsigned_to_nat(182);
    v___x_3303_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1;
    v___x_3304_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0;
    v___x_3305_ = l_mkPanicMessageWithDecl(
        v___x_3304_,
        v___x_3303_,
        v___x_3302_,
        v___x_3301_,
        v___x_3300_,
    );
    return v___x_3305_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2;
    v___x_3307_ = lean_unsigned_to_nat(21);
    v___x_3308_ = lean_unsigned_to_nat(183);
    v___x_3309_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1;
    v___x_3310_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0;
    v___x_3311_ = l_mkPanicMessageWithDecl(
        v___x_3310_,
        v___x_3309_,
        v___x_3308_,
        v___x_3307_,
        v___x_3306_,
    );
    return v___x_3311_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6;
    v___x_3315_ = lean_unsigned_to_nat(35);
    v___x_3316_ = lean_unsigned_to_nat(276);
    v___x_3317_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5;
    v___x_3318_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0;
    v___x_3319_ = l_mkPanicMessageWithDecl(
        v___x_3318_,
        v___x_3317_,
        v___x_3316_,
        v___x_3315_,
        v___x_3314_,
    );
    return v___x_3319_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8()
-> *mut LeanObject {
    let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6;
    v___x_3321_ = lean_unsigned_to_nat(21);
    v___x_3322_ = lean_unsigned_to_nat(277);
    v___x_3323_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5;
    v___x_3324_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0;
    v___x_3325_ = l_mkPanicMessageWithDecl(
        v___x_3324_,
        v___x_3323_,
        v___x_3322_,
        v___x_3321_,
        v___x_3320_,
    );
    return v___x_3325_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(
    mut v_k_3326_: *mut LeanObject,
    mut v_v_3327_: *mut LeanObject,
    mut v_t_3328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v_size_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_unused_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_unused_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut v_unused_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v_size_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_unused_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_unused_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v_k_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_unused_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut v_unused_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v_size_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_unused_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3586_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_unused_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v_unused_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v_size_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_k_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_unused_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_unused_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3668_: u8 = 0;
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_unused_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3328_) == 0 {
                    v_size_3329_ = lean_ctor_get(v_t_3328_, 0);
                    v_k_3330_ = lean_ctor_get(v_t_3328_, 1);
                    v_v_3331_ = lean_ctor_get(v_t_3328_, 2);
                    v_l_3332_ = lean_ctor_get(v_t_3328_, 3);
                    v_r_3333_ = lean_ctor_get(v_t_3328_, 4);
                    v_isSharedCheck_3689_ = (!lean_is_exclusive(v_t_3328_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v___x_3335_ = v_t_3328_;
                        v_isShared_3336_ = v_isSharedCheck_3689_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_3333_);
                        lean_inc(v_l_3332_);
                        lean_inc(v_v_3331_);
                        lean_inc(v_k_3330_);
                        lean_inc(v_size_3329_);
                        lean_dec(v_t_3328_);
                        v___x_3335_ = lean_box(0);
                        v_isShared_3336_ = v_isSharedCheck_3689_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3690_ = lean_unsigned_to_nat(1);
                    v___x_3691_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_3691_, 0, v___x_3690_);
                    lean_ctor_set(v___x_3691_, 1, v_k_3326_);
                    lean_ctor_set(v___x_3691_, 2, v_v_3327_);
                    lean_ctor_set(v___x_3691_, 3, v_t_3328_);
                    lean_ctor_set(v___x_3691_, 4, v_t_3328_);
                    return v___x_3691_;
                }
            }
            1 => {
                v___x_3337_ = lean_string_compare(v_k_3326_, v_k_3330_);
                match v___x_3337_ {
                    0 => {
                        lean_dec(v_size_3329_);
                        v___x_3338_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_3326_, v_v_3327_, v_l_3332_);
                        if lean_obj_tag(v_r_3333_) == 0 {
                            if lean_obj_tag(v___x_3338_) == 0 {
                                v_size_3339_ = lean_ctor_get(v_r_3333_, 0);
                                v_size_3340_ = lean_ctor_get(v___x_3338_, 0);
                                lean_inc(v_size_3340_);
                                v_k_3341_ = lean_ctor_get(v___x_3338_, 1);
                                lean_inc(v_k_3341_);
                                v_v_3342_ = lean_ctor_get(v___x_3338_, 2);
                                lean_inc(v_v_3342_);
                                v_l_3343_ = lean_ctor_get(v___x_3338_, 3);
                                lean_inc(v_l_3343_);
                                v_r_3344_ = lean_ctor_get(v___x_3338_, 4);
                                lean_inc(v_r_3344_);
                                v___x_3345_ = lean_unsigned_to_nat(3);
                                v___x_3346_ = lean_nat_mul(v___x_3345_, v_size_3339_);
                                v___x_3347_ = lean_nat_dec_lt(v___x_3346_, v_size_3340_);
                                lean_dec(v___x_3346_);
                                if v___x_3347_ == 0 {
                                    lean_dec(v_r_3344_);
                                    lean_dec(v_l_3343_);
                                    lean_dec(v_v_3342_);
                                    lean_dec(v_k_3341_);
                                    v___x_3348_ = lean_unsigned_to_nat(1);
                                    v___x_3349_ = lean_nat_add(v___x_3348_, v_size_3340_);
                                    lean_dec(v_size_3340_);
                                    v___x_3350_ = lean_nat_add(v___x_3349_, v_size_3339_);
                                    lean_dec(v___x_3349_);
                                    if v_isShared_3336_ == 0 {
                                        lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                        lean_ctor_set(v___x_3335_, 0, v___x_3350_);
                                        v___x_3352_ = v___x_3335_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3353_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3353_, 0, v___x_3350_);
                                        lean_ctor_set(v_reuseFailAlloc_3353_, 1, v_k_3330_);
                                        lean_ctor_set(v_reuseFailAlloc_3353_, 2, v_v_3331_);
                                        lean_ctor_set(v_reuseFailAlloc_3353_, 3, v___x_3338_);
                                        lean_ctor_set(v_reuseFailAlloc_3353_, 4, v_r_3333_);
                                        v___x_3352_ = v_reuseFailAlloc_3353_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3425_ = (!lean_is_exclusive(v___x_3338_)) as u8;
                                    if v_isSharedCheck_3425_ == 0 {
                                        v_unused_3426_ = lean_ctor_get(v___x_3338_, 4);
                                        lean_dec(v_unused_3426_);
                                        v_unused_3427_ = lean_ctor_get(v___x_3338_, 3);
                                        lean_dec(v_unused_3427_);
                                        v_unused_3428_ = lean_ctor_get(v___x_3338_, 2);
                                        lean_dec(v_unused_3428_);
                                        v_unused_3429_ = lean_ctor_get(v___x_3338_, 1);
                                        lean_dec(v_unused_3429_);
                                        v_unused_3430_ = lean_ctor_get(v___x_3338_, 0);
                                        lean_dec(v_unused_3430_);
                                        v___x_3355_ = v___x_3338_;
                                        v_isShared_3356_ = v_isSharedCheck_3425_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3338_);
                                        v___x_3355_ = lean_box(0);
                                        v_isShared_3356_ = v_isSharedCheck_3425_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3431_ = lean_ctor_get(v_r_3333_, 0);
                                v___x_3432_ = lean_unsigned_to_nat(1);
                                v___x_3433_ = lean_nat_add(v___x_3432_, v_size_3431_);
                                if v_isShared_3336_ == 0 {
                                    lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                    lean_ctor_set(v___x_3335_, 0, v___x_3433_);
                                    v___x_3435_ = v___x_3335_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3436_, 0, v___x_3433_);
                                    lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_k_3330_);
                                    lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_v_3331_);
                                    lean_ctor_set(v_reuseFailAlloc_3436_, 3, v___x_3338_);
                                    lean_ctor_set(v_reuseFailAlloc_3436_, 4, v_r_3333_);
                                    v___x_3435_ = v_reuseFailAlloc_3436_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_3338_) == 0 {
                                v_l_3437_ = lean_ctor_get(v___x_3338_, 3);
                                lean_inc(v_l_3437_);
                                if lean_obj_tag(v_l_3437_) == 0 {
                                    v_r_3438_ = lean_ctor_get(v___x_3338_, 4);
                                    lean_inc(v_r_3438_);
                                    if lean_obj_tag(v_r_3438_) == 0 {
                                        v_size_3439_ = lean_ctor_get(v___x_3338_, 0);
                                        v_k_3440_ = lean_ctor_get(v___x_3338_, 1);
                                        v_v_3441_ = lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3455_ =
                                            (!lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3455_ == 0 {
                                            v_unused_3456_ = lean_ctor_get(v___x_3338_, 4);
                                            lean_dec(v_unused_3456_);
                                            v_unused_3457_ = lean_ctor_get(v___x_3338_, 3);
                                            lean_dec(v_unused_3457_);
                                            v___x_3443_ = v___x_3338_;
                                            v_isShared_3444_ = v_isSharedCheck_3455_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3441_);
                                            lean_inc(v_k_3440_);
                                            lean_inc(v_size_3439_);
                                            lean_dec(v___x_3338_);
                                            v___x_3443_ = lean_box(0);
                                            v_isShared_3444_ = v_isSharedCheck_3455_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3458_ = lean_ctor_get(v___x_3338_, 1);
                                        v_v_3459_ = lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3471_ =
                                            (!lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3471_ == 0 {
                                            v_unused_3472_ = lean_ctor_get(v___x_3338_, 4);
                                            lean_dec(v_unused_3472_);
                                            v_unused_3473_ = lean_ctor_get(v___x_3338_, 3);
                                            lean_dec(v_unused_3473_);
                                            v_unused_3474_ = lean_ctor_get(v___x_3338_, 0);
                                            lean_dec(v_unused_3474_);
                                            v___x_3461_ = v___x_3338_;
                                            v_isShared_3462_ = v_isSharedCheck_3471_;
                                            state = 17;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3459_);
                                            lean_inc(v_k_3458_);
                                            lean_dec(v___x_3338_);
                                            v___x_3461_ = lean_box(0);
                                            v_isShared_3462_ = v_isSharedCheck_3471_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3475_ = lean_ctor_get(v___x_3338_, 4);
                                    lean_inc(v_r_3475_);
                                    if lean_obj_tag(v_r_3475_) == 0 {
                                        v_k_3476_ = lean_ctor_get(v___x_3338_, 1);
                                        v_v_3477_ = lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3501_ =
                                            (!lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3501_ == 0 {
                                            v_unused_3502_ = lean_ctor_get(v___x_3338_, 4);
                                            lean_dec(v_unused_3502_);
                                            v_unused_3503_ = lean_ctor_get(v___x_3338_, 3);
                                            lean_dec(v_unused_3503_);
                                            v_unused_3504_ = lean_ctor_get(v___x_3338_, 0);
                                            lean_dec(v_unused_3504_);
                                            v___x_3479_ = v___x_3338_;
                                            v_isShared_3480_ = v_isSharedCheck_3501_;
                                            state = 20;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3477_);
                                            lean_inc(v_k_3476_);
                                            lean_dec(v___x_3338_);
                                            v___x_3479_ = lean_box(0);
                                            v_isShared_3480_ = v_isSharedCheck_3501_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_3505_ = lean_unsigned_to_nat(2);
                                        if v_isShared_3336_ == 0 {
                                            lean_ctor_set(v___x_3335_, 4, v_r_3475_);
                                            lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                            lean_ctor_set(v___x_3335_, 0, v___x_3505_);
                                            v___x_3507_ = v___x_3335_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3508_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
                                            lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3330_);
                                            lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3331_);
                                            lean_ctor_set(v_reuseFailAlloc_3508_, 3, v___x_3338_);
                                            lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3475_);
                                            v___x_3507_ = v_reuseFailAlloc_3508_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3509_ = lean_unsigned_to_nat(1);
                                if v_isShared_3336_ == 0 {
                                    lean_ctor_set(v___x_3335_, 4, v___x_3338_);
                                    lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                    lean_ctor_set(v___x_3335_, 0, v___x_3509_);
                                    v___x_3511_ = v___x_3335_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3512_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3512_, 0, v___x_3509_);
                                    lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_k_3330_);
                                    lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_v_3331_);
                                    lean_ctor_set(v_reuseFailAlloc_3512_, 3, v___x_3338_);
                                    lean_ctor_set(v_reuseFailAlloc_3512_, 4, v___x_3338_);
                                    v___x_3511_ = v_reuseFailAlloc_3512_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        lean_dec(v_v_3331_);
                        lean_dec(v_k_3330_);
                        if v_isShared_3336_ == 0 {
                            lean_ctor_set(v___x_3335_, 2, v_v_3327_);
                            lean_ctor_set(v___x_3335_, 1, v_k_3326_);
                            v___x_3514_ = v___x_3335_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_size_3329_);
                            lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3326_);
                            lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3327_);
                            lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_l_3332_);
                            lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_r_3333_);
                            v___x_3514_ = v_reuseFailAlloc_3515_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        lean_dec(v_size_3329_);
                        v___x_3516_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_3326_, v_v_3327_, v_r_3333_);
                        if lean_obj_tag(v_l_3332_) == 0 {
                            if lean_obj_tag(v___x_3516_) == 0 {
                                v_size_3517_ = lean_ctor_get(v_l_3332_, 0);
                                v_size_3518_ = lean_ctor_get(v___x_3516_, 0);
                                lean_inc(v_size_3518_);
                                v_k_3519_ = lean_ctor_get(v___x_3516_, 1);
                                lean_inc(v_k_3519_);
                                v_v_3520_ = lean_ctor_get(v___x_3516_, 2);
                                lean_inc(v_v_3520_);
                                v_l_3521_ = lean_ctor_get(v___x_3516_, 3);
                                lean_inc(v_l_3521_);
                                v_r_3522_ = lean_ctor_get(v___x_3516_, 4);
                                lean_inc(v_r_3522_);
                                v___x_3523_ = lean_unsigned_to_nat(3);
                                v___x_3524_ = lean_nat_mul(v___x_3523_, v_size_3517_);
                                v___x_3525_ = lean_nat_dec_lt(v___x_3524_, v_size_3518_);
                                lean_dec(v___x_3524_);
                                if v___x_3525_ == 0 {
                                    lean_dec(v_r_3522_);
                                    lean_dec(v_l_3521_);
                                    lean_dec(v_v_3520_);
                                    lean_dec(v_k_3519_);
                                    v___x_3526_ = lean_unsigned_to_nat(1);
                                    v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3517_);
                                    v___x_3528_ = lean_nat_add(v___x_3527_, v_size_3518_);
                                    lean_dec(v_size_3518_);
                                    lean_dec(v___x_3527_);
                                    if v_isShared_3336_ == 0 {
                                        lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                        lean_ctor_set(v___x_3335_, 0, v___x_3528_);
                                        v___x_3530_ = v___x_3335_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 1, v_k_3330_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 2, v_v_3331_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 3, v_l_3332_);
                                        lean_ctor_set(v_reuseFailAlloc_3531_, 4, v___x_3516_);
                                        v___x_3530_ = v_reuseFailAlloc_3531_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3601_ = (!lean_is_exclusive(v___x_3516_)) as u8;
                                    if v_isSharedCheck_3601_ == 0 {
                                        v_unused_3602_ = lean_ctor_get(v___x_3516_, 4);
                                        lean_dec(v_unused_3602_);
                                        v_unused_3603_ = lean_ctor_get(v___x_3516_, 3);
                                        lean_dec(v_unused_3603_);
                                        v_unused_3604_ = lean_ctor_get(v___x_3516_, 2);
                                        lean_dec(v_unused_3604_);
                                        v_unused_3605_ = lean_ctor_get(v___x_3516_, 1);
                                        lean_dec(v_unused_3605_);
                                        v_unused_3606_ = lean_ctor_get(v___x_3516_, 0);
                                        lean_dec(v_unused_3606_);
                                        v___x_3533_ = v___x_3516_;
                                        v_isShared_3534_ = v_isSharedCheck_3601_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3516_);
                                        v___x_3533_ = lean_box(0);
                                        v_isShared_3534_ = v_isSharedCheck_3601_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3607_ = lean_ctor_get(v_l_3332_, 0);
                                v___x_3608_ = lean_unsigned_to_nat(1);
                                v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3607_);
                                if v_isShared_3336_ == 0 {
                                    lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                    lean_ctor_set(v___x_3335_, 0, v___x_3609_);
                                    v___x_3611_ = v___x_3335_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3609_);
                                    lean_ctor_set(v_reuseFailAlloc_3612_, 1, v_k_3330_);
                                    lean_ctor_set(v_reuseFailAlloc_3612_, 2, v_v_3331_);
                                    lean_ctor_set(v_reuseFailAlloc_3612_, 3, v_l_3332_);
                                    lean_ctor_set(v_reuseFailAlloc_3612_, 4, v___x_3516_);
                                    v___x_3611_ = v_reuseFailAlloc_3612_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if lean_obj_tag(v___x_3516_) == 0 {
                                v_l_3613_ = lean_ctor_get(v___x_3516_, 3);
                                lean_inc(v_l_3613_);
                                if lean_obj_tag(v_l_3613_) == 0 {
                                    v_r_3614_ = lean_ctor_get(v___x_3516_, 4);
                                    lean_inc(v_r_3614_);
                                    if lean_obj_tag(v_r_3614_) == 0 {
                                        v_size_3615_ = lean_ctor_get(v___x_3516_, 0);
                                        v_k_3616_ = lean_ctor_get(v___x_3516_, 1);
                                        v_v_3617_ = lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3631_ =
                                            (!lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3631_ == 0 {
                                            v_unused_3632_ = lean_ctor_get(v___x_3516_, 4);
                                            lean_dec(v_unused_3632_);
                                            v_unused_3633_ = lean_ctor_get(v___x_3516_, 3);
                                            lean_dec(v_unused_3633_);
                                            v___x_3619_ = v___x_3516_;
                                            v_isShared_3620_ = v_isSharedCheck_3631_;
                                            state = 40;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3617_);
                                            lean_inc(v_k_3616_);
                                            lean_inc(v_size_3615_);
                                            lean_dec(v___x_3516_);
                                            v___x_3619_ = lean_box(0);
                                            v_isShared_3620_ = v_isSharedCheck_3631_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3634_ = lean_ctor_get(v___x_3516_, 1);
                                        v_v_3635_ = lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3659_ =
                                            (!lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3659_ == 0 {
                                            v_unused_3660_ = lean_ctor_get(v___x_3516_, 4);
                                            lean_dec(v_unused_3660_);
                                            v_unused_3661_ = lean_ctor_get(v___x_3516_, 3);
                                            lean_dec(v_unused_3661_);
                                            v_unused_3662_ = lean_ctor_get(v___x_3516_, 0);
                                            lean_dec(v_unused_3662_);
                                            v___x_3637_ = v___x_3516_;
                                            v_isShared_3638_ = v_isSharedCheck_3659_;
                                            state = 43;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3635_);
                                            lean_inc(v_k_3634_);
                                            lean_dec(v___x_3516_);
                                            v___x_3637_ = lean_box(0);
                                            v_isShared_3638_ = v_isSharedCheck_3659_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3663_ = lean_ctor_get(v___x_3516_, 4);
                                    lean_inc(v_r_3663_);
                                    if lean_obj_tag(v_r_3663_) == 0 {
                                        v_k_3664_ = lean_ctor_get(v___x_3516_, 1);
                                        v_v_3665_ = lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3677_ =
                                            (!lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3677_ == 0 {
                                            v_unused_3678_ = lean_ctor_get(v___x_3516_, 4);
                                            lean_dec(v_unused_3678_);
                                            v_unused_3679_ = lean_ctor_get(v___x_3516_, 3);
                                            lean_dec(v_unused_3679_);
                                            v_unused_3680_ = lean_ctor_get(v___x_3516_, 0);
                                            lean_dec(v_unused_3680_);
                                            v___x_3667_ = v___x_3516_;
                                            v_isShared_3668_ = v_isSharedCheck_3677_;
                                            state = 48;
                                            continue;
                                        } else {
                                            lean_inc(v_v_3665_);
                                            lean_inc(v_k_3664_);
                                            lean_dec(v___x_3516_);
                                            v___x_3667_ = lean_box(0);
                                            v_isShared_3668_ = v_isSharedCheck_3677_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_3681_ = lean_unsigned_to_nat(2);
                                        if v_isShared_3336_ == 0 {
                                            lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                            lean_ctor_set(v___x_3335_, 3, v_r_3663_);
                                            lean_ctor_set(v___x_3335_, 0, v___x_3681_);
                                            v___x_3683_ = v___x_3335_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3684_ =
                                                lean_alloc_ctor(0, 5, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
                                            lean_ctor_set(v_reuseFailAlloc_3684_, 1, v_k_3330_);
                                            lean_ctor_set(v_reuseFailAlloc_3684_, 2, v_v_3331_);
                                            lean_ctor_set(v_reuseFailAlloc_3684_, 3, v_r_3663_);
                                            lean_ctor_set(v_reuseFailAlloc_3684_, 4, v___x_3516_);
                                            v___x_3683_ = v_reuseFailAlloc_3684_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3685_ = lean_unsigned_to_nat(1);
                                if v_isShared_3336_ == 0 {
                                    lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                    lean_ctor_set(v___x_3335_, 3, v___x_3516_);
                                    lean_ctor_set(v___x_3335_, 0, v___x_3685_);
                                    v___x_3687_ = v___x_3335_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
                                    lean_ctor_set(v_reuseFailAlloc_3688_, 1, v_k_3330_);
                                    lean_ctor_set(v_reuseFailAlloc_3688_, 2, v_v_3331_);
                                    lean_ctor_set(v_reuseFailAlloc_3688_, 3, v___x_3516_);
                                    lean_ctor_set(v_reuseFailAlloc_3688_, 4, v___x_3516_);
                                    v___x_3687_ = v_reuseFailAlloc_3688_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3352_;
            }
            3 => {
                if lean_obj_tag(v_l_3343_) == 0 {
                    if lean_obj_tag(v_r_3344_) == 0 {
                        v_size_3357_ = lean_ctor_get(v_l_3343_, 0);
                        v_size_3358_ = lean_ctor_get(v_r_3344_, 0);
                        v_k_3359_ = lean_ctor_get(v_r_3344_, 1);
                        v_v_3360_ = lean_ctor_get(v_r_3344_, 2);
                        v_l_3361_ = lean_ctor_get(v_r_3344_, 3);
                        v_r_3362_ = lean_ctor_get(v_r_3344_, 4);
                        v___x_3363_ = lean_unsigned_to_nat(2);
                        v___x_3364_ = lean_nat_mul(v___x_3363_, v_size_3357_);
                        v___x_3365_ = lean_nat_dec_lt(v_size_3358_, v___x_3364_);
                        lean_dec(v___x_3364_);
                        if v___x_3365_ == 0 {
                            lean_inc(v_r_3362_);
                            lean_inc(v_l_3361_);
                            lean_inc(v_v_3360_);
                            lean_inc(v_k_3359_);
                            v_isSharedCheck_3395_ = (!lean_is_exclusive(v_r_3344_)) as u8;
                            if v_isSharedCheck_3395_ == 0 {
                                v_unused_3396_ = lean_ctor_get(v_r_3344_, 4);
                                lean_dec(v_unused_3396_);
                                v_unused_3397_ = lean_ctor_get(v_r_3344_, 3);
                                lean_dec(v_unused_3397_);
                                v_unused_3398_ = lean_ctor_get(v_r_3344_, 2);
                                lean_dec(v_unused_3398_);
                                v_unused_3399_ = lean_ctor_get(v_r_3344_, 1);
                                lean_dec(v_unused_3399_);
                                v_unused_3400_ = lean_ctor_get(v_r_3344_, 0);
                                lean_dec(v_unused_3400_);
                                v___x_3367_ = v_r_3344_;
                                v_isShared_3368_ = v_isSharedCheck_3395_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v_r_3344_);
                                v___x_3367_ = lean_box(0);
                                v_isShared_3368_ = v_isSharedCheck_3395_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3335_);
                            v___x_3401_ = lean_unsigned_to_nat(1);
                            v___x_3402_ = lean_nat_add(v___x_3401_, v_size_3340_);
                            lean_dec(v_size_3340_);
                            v___x_3403_ = lean_nat_add(v___x_3402_, v_size_3339_);
                            lean_dec(v___x_3402_);
                            v___x_3404_ = lean_nat_add(v___x_3401_, v_size_3339_);
                            v___x_3405_ = lean_nat_add(v___x_3404_, v_size_3358_);
                            lean_dec(v___x_3404_);
                            lean_inc_ref(v_r_3333_);
                            if v_isShared_3356_ == 0 {
                                lean_ctor_set(v___x_3355_, 4, v_r_3333_);
                                lean_ctor_set(v___x_3355_, 3, v_r_3344_);
                                lean_ctor_set(v___x_3355_, 2, v_v_3331_);
                                lean_ctor_set(v___x_3355_, 1, v_k_3330_);
                                lean_ctor_set(v___x_3355_, 0, v___x_3405_);
                                v___x_3407_ = v___x_3355_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3405_);
                                lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_k_3330_);
                                lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_v_3331_);
                                lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_r_3344_);
                                lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_r_3333_);
                                v___x_3407_ = v_reuseFailAlloc_3420_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_3343_, 5);
                        lean_del_object(v___x_3355_);
                        lean_dec(v_v_3342_);
                        lean_dec(v_k_3341_);
                        lean_dec(v_size_3340_);
                        lean_dec_ref_known(v_r_3333_, 5);
                        lean_del_object(v___x_3335_);
                        lean_dec(v_v_3331_);
                        lean_dec(v_k_3330_);
                        v___x_3421_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
                        v___x_3422_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3421_);
                        return v___x_3422_;
                    }
                } else {
                    lean_del_object(v___x_3355_);
                    lean_dec(v_r_3344_);
                    lean_dec(v_v_3342_);
                    lean_dec(v_k_3341_);
                    lean_dec(v_size_3340_);
                    lean_dec_ref_known(v_r_3333_, 5);
                    lean_del_object(v___x_3335_);
                    lean_dec(v_v_3331_);
                    lean_dec(v_k_3330_);
                    v___x_3423_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
                    v___x_3424_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3423_);
                    return v___x_3424_;
                }
            }
            4 => {
                v___x_3369_ = lean_unsigned_to_nat(1);
                v___x_3370_ = lean_nat_add(v___x_3369_, v_size_3340_);
                lean_dec(v_size_3340_);
                v___x_3371_ = lean_nat_add(v___x_3370_, v_size_3339_);
                lean_dec(v___x_3370_);
                v___x_3383_ = lean_nat_add(v___x_3369_, v_size_3357_);
                if lean_obj_tag(v_l_3361_) == 0 {
                    v_size_3393_ = lean_ctor_get(v_l_3361_, 0);
                    lean_inc(v_size_3393_);
                    v___y_3385_ = v_size_3393_;
                    state = 8;
                    continue;
                } else {
                    v___x_3394_ = lean_unsigned_to_nat(0);
                    v___y_3385_ = v___x_3394_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3376_ = lean_nat_add(v___y_3374_, v___y_3375_);
                lean_dec(v___y_3375_);
                lean_dec(v___y_3374_);
                if v_isShared_3368_ == 0 {
                    lean_ctor_set(v___x_3367_, 4, v_r_3333_);
                    lean_ctor_set(v___x_3367_, 3, v_r_3362_);
                    lean_ctor_set(v___x_3367_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3367_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3367_, 0, v___x_3376_);
                    v___x_3378_ = v___x_3367_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3376_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_r_3362_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_r_3333_);
                    v___x_3378_ = v_reuseFailAlloc_3382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3356_ == 0 {
                    lean_ctor_set(v___x_3355_, 4, v___x_3378_);
                    lean_ctor_set(v___x_3355_, 3, v___y_3373_);
                    lean_ctor_set(v___x_3355_, 2, v_v_3360_);
                    lean_ctor_set(v___x_3355_, 1, v_k_3359_);
                    lean_ctor_set(v___x_3355_, 0, v___x_3371_);
                    v___x_3380_ = v___x_3355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3371_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3359_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3360_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 3, v___y_3373_);
                    lean_ctor_set(v_reuseFailAlloc_3381_, 4, v___x_3378_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3380_;
            }
            8 => {
                v___x_3386_ = lean_nat_add(v___x_3383_, v___y_3385_);
                lean_dec(v___y_3385_);
                lean_dec(v___x_3383_);
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v_l_3361_);
                    lean_ctor_set(v___x_3335_, 3, v_l_3343_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3342_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3341_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3335_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3341_);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3342_);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_l_3343_);
                    lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_l_3361_);
                    v___x_3388_ = v_reuseFailAlloc_3392_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3389_ = lean_nat_add(v___x_3369_, v_size_3339_);
                if lean_obj_tag(v_r_3362_) == 0 {
                    v_size_3390_ = lean_ctor_get(v_r_3362_, 0);
                    lean_inc(v_size_3390_);
                    v___y_3373_ = v___x_3388_;
                    v___y_3374_ = v___x_3389_;
                    v___y_3375_ = v_size_3390_;
                    state = 5;
                    continue;
                } else {
                    v___x_3391_ = lean_unsigned_to_nat(0);
                    v___y_3373_ = v___x_3388_;
                    v___y_3374_ = v___x_3389_;
                    v___y_3375_ = v___x_3391_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3414_ = (!lean_is_exclusive(v_r_3333_)) as u8;
                if v_isSharedCheck_3414_ == 0 {
                    v_unused_3415_ = lean_ctor_get(v_r_3333_, 4);
                    lean_dec(v_unused_3415_);
                    v_unused_3416_ = lean_ctor_get(v_r_3333_, 3);
                    lean_dec(v_unused_3416_);
                    v_unused_3417_ = lean_ctor_get(v_r_3333_, 2);
                    lean_dec(v_unused_3417_);
                    v_unused_3418_ = lean_ctor_get(v_r_3333_, 1);
                    lean_dec(v_unused_3418_);
                    v_unused_3419_ = lean_ctor_get(v_r_3333_, 0);
                    lean_dec(v_unused_3419_);
                    v___x_3409_ = v_r_3333_;
                    v_isShared_3410_ = v_isSharedCheck_3414_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_r_3333_);
                    v___x_3409_ = lean_box(0);
                    v_isShared_3410_ = v_isSharedCheck_3414_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3410_ == 0 {
                    lean_ctor_set(v___x_3409_, 4, v___x_3407_);
                    lean_ctor_set(v___x_3409_, 3, v_l_3343_);
                    lean_ctor_set(v___x_3409_, 2, v_v_3342_);
                    lean_ctor_set(v___x_3409_, 1, v_k_3341_);
                    lean_ctor_set(v___x_3409_, 0, v___x_3403_);
                    v___x_3412_ = v___x_3409_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3403_);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_k_3341_);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_v_3342_);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_l_3343_);
                    lean_ctor_set(v_reuseFailAlloc_3413_, 4, v___x_3407_);
                    v___x_3412_ = v_reuseFailAlloc_3413_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3412_;
            }
            13 => {
                return v___x_3435_;
            }
            14 => {
                v_size_3445_ = lean_ctor_get(v_r_3438_, 0);
                v___x_3446_ = lean_unsigned_to_nat(1);
                v___x_3447_ = lean_nat_add(v___x_3446_, v_size_3439_);
                lean_dec(v_size_3439_);
                v___x_3448_ = lean_nat_add(v___x_3446_, v_size_3445_);
                if v_isShared_3444_ == 0 {
                    lean_ctor_set(v___x_3443_, 4, v_r_3333_);
                    lean_ctor_set(v___x_3443_, 3, v_r_3438_);
                    lean_ctor_set(v___x_3443_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3443_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3443_, 0, v___x_3448_);
                    v___x_3450_ = v___x_3443_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_r_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_r_3333_);
                    v___x_3450_ = v_reuseFailAlloc_3454_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v___x_3450_);
                    lean_ctor_set(v___x_3335_, 3, v_l_3437_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3441_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3440_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3447_);
                    v___x_3452_ = v___x_3335_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3447_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3440_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3441_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_l_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3453_, 4, v___x_3450_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3452_;
            }
            17 => {
                v___x_3463_ = lean_unsigned_to_nat(3);
                v___x_3464_ = lean_unsigned_to_nat(1);
                if v_isShared_3462_ == 0 {
                    lean_ctor_set(v___x_3461_, 3, v_r_3438_);
                    lean_ctor_set(v___x_3461_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3461_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3461_, 0, v___x_3464_);
                    v___x_3466_ = v___x_3461_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3464_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_r_3438_);
                    lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_r_3438_);
                    v___x_3466_ = v_reuseFailAlloc_3470_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v___x_3466_);
                    lean_ctor_set(v___x_3335_, 3, v_l_3437_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3459_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3458_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3463_);
                    v___x_3468_ = v___x_3335_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3458_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3459_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_l_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3469_, 4, v___x_3466_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3468_;
            }
            20 => {
                v_k_3481_ = lean_ctor_get(v_r_3475_, 1);
                v_v_3482_ = lean_ctor_get(v_r_3475_, 2);
                v_isSharedCheck_3497_ = (!lean_is_exclusive(v_r_3475_)) as u8;
                if v_isSharedCheck_3497_ == 0 {
                    v_unused_3498_ = lean_ctor_get(v_r_3475_, 4);
                    lean_dec(v_unused_3498_);
                    v_unused_3499_ = lean_ctor_get(v_r_3475_, 3);
                    lean_dec(v_unused_3499_);
                    v_unused_3500_ = lean_ctor_get(v_r_3475_, 0);
                    lean_dec(v_unused_3500_);
                    v___x_3484_ = v_r_3475_;
                    v_isShared_3485_ = v_isSharedCheck_3497_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_v_3482_);
                    lean_inc(v_k_3481_);
                    lean_dec(v_r_3475_);
                    v___x_3484_ = lean_box(0);
                    v_isShared_3485_ = v_isSharedCheck_3497_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3486_ = lean_unsigned_to_nat(3);
                v___x_3487_ = lean_unsigned_to_nat(1);
                if v_isShared_3485_ == 0 {
                    lean_ctor_set(v___x_3484_, 4, v_l_3437_);
                    lean_ctor_set(v___x_3484_, 3, v_l_3437_);
                    lean_ctor_set(v___x_3484_, 2, v_v_3477_);
                    lean_ctor_set(v___x_3484_, 1, v_k_3476_);
                    lean_ctor_set(v___x_3484_, 0, v___x_3487_);
                    v___x_3489_ = v___x_3484_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3487_);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3476_);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3477_);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_l_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_l_3437_);
                    v___x_3489_ = v_reuseFailAlloc_3496_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_3480_ == 0 {
                    lean_ctor_set(v___x_3479_, 4, v_l_3437_);
                    lean_ctor_set(v___x_3479_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3479_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3479_, 0, v___x_3487_);
                    v___x_3491_ = v___x_3479_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3487_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_l_3437_);
                    lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_l_3437_);
                    v___x_3491_ = v_reuseFailAlloc_3495_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v___x_3491_);
                    lean_ctor_set(v___x_3335_, 3, v___x_3489_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3482_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3481_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3486_);
                    v___x_3493_ = v___x_3335_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3481_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3482_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 3, v___x_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
                    v___x_3493_ = v_reuseFailAlloc_3494_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3493_;
            }
            25 => {
                return v___x_3507_;
            }
            26 => {
                return v___x_3511_;
            }
            27 => {
                return v___x_3514_;
            }
            28 => {
                return v___x_3530_;
            }
            29 => {
                if lean_obj_tag(v_l_3521_) == 0 {
                    if lean_obj_tag(v_r_3522_) == 0 {
                        v_size_3535_ = lean_ctor_get(v_l_3521_, 0);
                        v_k_3536_ = lean_ctor_get(v_l_3521_, 1);
                        v_v_3537_ = lean_ctor_get(v_l_3521_, 2);
                        v_l_3538_ = lean_ctor_get(v_l_3521_, 3);
                        v_r_3539_ = lean_ctor_get(v_l_3521_, 4);
                        v_size_3540_ = lean_ctor_get(v_r_3522_, 0);
                        v___x_3541_ = lean_unsigned_to_nat(2);
                        v___x_3542_ = lean_nat_mul(v___x_3541_, v_size_3540_);
                        v___x_3543_ = lean_nat_dec_lt(v_size_3535_, v___x_3542_);
                        lean_dec(v___x_3542_);
                        if v___x_3543_ == 0 {
                            lean_inc(v_r_3539_);
                            lean_inc(v_l_3538_);
                            lean_inc(v_v_3537_);
                            lean_inc(v_k_3536_);
                            v_isSharedCheck_3572_ = (!lean_is_exclusive(v_l_3521_)) as u8;
                            if v_isSharedCheck_3572_ == 0 {
                                v_unused_3573_ = lean_ctor_get(v_l_3521_, 4);
                                lean_dec(v_unused_3573_);
                                v_unused_3574_ = lean_ctor_get(v_l_3521_, 3);
                                lean_dec(v_unused_3574_);
                                v_unused_3575_ = lean_ctor_get(v_l_3521_, 2);
                                lean_dec(v_unused_3575_);
                                v_unused_3576_ = lean_ctor_get(v_l_3521_, 1);
                                lean_dec(v_unused_3576_);
                                v_unused_3577_ = lean_ctor_get(v_l_3521_, 0);
                                lean_dec(v_unused_3577_);
                                v___x_3545_ = v_l_3521_;
                                v_isShared_3546_ = v_isSharedCheck_3572_;
                                state = 30;
                                continue;
                            } else {
                                lean_dec(v_l_3521_);
                                v___x_3545_ = lean_box(0);
                                v_isShared_3546_ = v_isSharedCheck_3572_;
                                state = 30;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_3335_);
                            v___x_3578_ = lean_unsigned_to_nat(1);
                            v___x_3579_ = lean_nat_add(v___x_3578_, v_size_3517_);
                            v___x_3580_ = lean_nat_add(v___x_3579_, v_size_3518_);
                            lean_dec(v_size_3518_);
                            v___x_3581_ = lean_nat_add(v___x_3579_, v_size_3535_);
                            lean_dec(v___x_3579_);
                            lean_inc_ref(v_l_3332_);
                            if v_isShared_3534_ == 0 {
                                lean_ctor_set(v___x_3533_, 4, v_l_3521_);
                                lean_ctor_set(v___x_3533_, 3, v_l_3332_);
                                lean_ctor_set(v___x_3533_, 2, v_v_3331_);
                                lean_ctor_set(v___x_3533_, 1, v_k_3330_);
                                lean_ctor_set(v___x_3533_, 0, v___x_3581_);
                                v___x_3583_ = v___x_3533_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3596_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3581_);
                                lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3330_);
                                lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3331_);
                                lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_l_3332_);
                                lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_l_3521_);
                                v___x_3583_ = v_reuseFailAlloc_3596_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_l_3521_, 5);
                        lean_del_object(v___x_3533_);
                        lean_dec(v_v_3520_);
                        lean_dec(v_k_3519_);
                        lean_dec(v_size_3518_);
                        lean_dec_ref_known(v_l_3332_, 5);
                        lean_del_object(v___x_3335_);
                        lean_dec(v_v_3331_);
                        lean_dec(v_k_3330_);
                        v___x_3597_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
                        v___x_3598_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3597_);
                        return v___x_3598_;
                    }
                } else {
                    lean_del_object(v___x_3533_);
                    lean_dec(v_r_3522_);
                    lean_dec(v_v_3520_);
                    lean_dec(v_k_3519_);
                    lean_dec(v_size_3518_);
                    lean_dec_ref_known(v_l_3332_, 5);
                    lean_del_object(v___x_3335_);
                    lean_dec(v_v_3331_);
                    lean_dec(v_k_3330_);
                    v___x_3599_ = lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
                    v___x_3600_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3599_);
                    return v___x_3600_;
                }
            }
            30 => {
                v___x_3547_ = lean_unsigned_to_nat(1);
                v___x_3548_ = lean_nat_add(v___x_3547_, v_size_3517_);
                v___x_3549_ = lean_nat_add(v___x_3548_, v_size_3518_);
                lean_dec(v_size_3518_);
                if lean_obj_tag(v_l_3538_) == 0 {
                    v_size_3570_ = lean_ctor_get(v_l_3538_, 0);
                    lean_inc(v_size_3570_);
                    v___y_3562_ = v_size_3570_;
                    state = 34;
                    continue;
                } else {
                    v___x_3571_ = lean_unsigned_to_nat(0);
                    v___y_3562_ = v___x_3571_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3554_ = lean_nat_add(v___y_3552_, v___y_3553_);
                lean_dec(v___y_3553_);
                lean_dec(v___y_3552_);
                if v_isShared_3546_ == 0 {
                    lean_ctor_set(v___x_3545_, 4, v_r_3522_);
                    lean_ctor_set(v___x_3545_, 3, v_r_3539_);
                    lean_ctor_set(v___x_3545_, 2, v_v_3520_);
                    lean_ctor_set(v___x_3545_, 1, v_k_3519_);
                    lean_ctor_set(v___x_3545_, 0, v___x_3554_);
                    v___x_3556_ = v___x_3545_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3554_);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_k_3519_);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_v_3520_);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_r_3539_);
                    lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_r_3522_);
                    v___x_3556_ = v_reuseFailAlloc_3560_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3534_ == 0 {
                    lean_ctor_set(v___x_3533_, 4, v___x_3556_);
                    lean_ctor_set(v___x_3533_, 3, v___y_3551_);
                    lean_ctor_set(v___x_3533_, 2, v_v_3537_);
                    lean_ctor_set(v___x_3533_, 1, v_k_3536_);
                    lean_ctor_set(v___x_3533_, 0, v___x_3549_);
                    v___x_3558_ = v___x_3533_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3549_);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_k_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_v_3537_);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 3, v___y_3551_);
                    lean_ctor_set(v_reuseFailAlloc_3559_, 4, v___x_3556_);
                    v___x_3558_ = v_reuseFailAlloc_3559_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3558_;
            }
            34 => {
                v___x_3563_ = lean_nat_add(v___x_3548_, v___y_3562_);
                lean_dec(v___y_3562_);
                lean_dec(v___x_3548_);
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v_l_3538_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3563_);
                    v___x_3565_ = v___x_3335_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_l_3332_);
                    lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_l_3538_);
                    v___x_3565_ = v_reuseFailAlloc_3569_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3566_ = lean_nat_add(v___x_3547_, v_size_3540_);
                if lean_obj_tag(v_r_3539_) == 0 {
                    v_size_3567_ = lean_ctor_get(v_r_3539_, 0);
                    lean_inc(v_size_3567_);
                    v___y_3551_ = v___x_3565_;
                    v___y_3552_ = v___x_3566_;
                    v___y_3553_ = v_size_3567_;
                    state = 31;
                    continue;
                } else {
                    v___x_3568_ = lean_unsigned_to_nat(0);
                    v___y_3551_ = v___x_3565_;
                    v___y_3552_ = v___x_3566_;
                    v___y_3553_ = v___x_3568_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3590_ = (!lean_is_exclusive(v_l_3332_)) as u8;
                if v_isSharedCheck_3590_ == 0 {
                    v_unused_3591_ = lean_ctor_get(v_l_3332_, 4);
                    lean_dec(v_unused_3591_);
                    v_unused_3592_ = lean_ctor_get(v_l_3332_, 3);
                    lean_dec(v_unused_3592_);
                    v_unused_3593_ = lean_ctor_get(v_l_3332_, 2);
                    lean_dec(v_unused_3593_);
                    v_unused_3594_ = lean_ctor_get(v_l_3332_, 1);
                    lean_dec(v_unused_3594_);
                    v_unused_3595_ = lean_ctor_get(v_l_3332_, 0);
                    lean_dec(v_unused_3595_);
                    v___x_3585_ = v_l_3332_;
                    v_isShared_3586_ = v_isSharedCheck_3590_;
                    state = 37;
                    continue;
                } else {
                    lean_dec(v_l_3332_);
                    v___x_3585_ = lean_box(0);
                    v_isShared_3586_ = v_isSharedCheck_3590_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3586_ == 0 {
                    lean_ctor_set(v___x_3585_, 4, v_r_3522_);
                    lean_ctor_set(v___x_3585_, 3, v___x_3583_);
                    lean_ctor_set(v___x_3585_, 2, v_v_3520_);
                    lean_ctor_set(v___x_3585_, 1, v_k_3519_);
                    lean_ctor_set(v___x_3585_, 0, v___x_3580_);
                    v___x_3588_ = v___x_3585_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3580_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_k_3519_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_v_3520_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3583_);
                    lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_r_3522_);
                    v___x_3588_ = v_reuseFailAlloc_3589_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3588_;
            }
            39 => {
                return v___x_3611_;
            }
            40 => {
                v_size_3621_ = lean_ctor_get(v_l_3613_, 0);
                v___x_3622_ = lean_unsigned_to_nat(1);
                v___x_3623_ = lean_nat_add(v___x_3622_, v_size_3615_);
                lean_dec(v_size_3615_);
                v___x_3624_ = lean_nat_add(v___x_3622_, v_size_3621_);
                if v_isShared_3620_ == 0 {
                    lean_ctor_set(v___x_3619_, 4, v_l_3613_);
                    lean_ctor_set(v___x_3619_, 3, v_l_3332_);
                    lean_ctor_set(v___x_3619_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3619_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3619_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3619_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3332_);
                    lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_l_3613_);
                    v___x_3626_ = v_reuseFailAlloc_3630_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v_r_3614_);
                    lean_ctor_set(v___x_3335_, 3, v___x_3626_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3617_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3616_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3623_);
                    v___x_3628_ = v___x_3335_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3623_);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3616_);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3617_);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 3, v___x_3626_);
                    lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_r_3614_);
                    v___x_3628_ = v_reuseFailAlloc_3629_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3628_;
            }
            43 => {
                v_k_3639_ = lean_ctor_get(v_l_3613_, 1);
                v_v_3640_ = lean_ctor_get(v_l_3613_, 2);
                v_isSharedCheck_3655_ = (!lean_is_exclusive(v_l_3613_)) as u8;
                if v_isSharedCheck_3655_ == 0 {
                    v_unused_3656_ = lean_ctor_get(v_l_3613_, 4);
                    lean_dec(v_unused_3656_);
                    v_unused_3657_ = lean_ctor_get(v_l_3613_, 3);
                    lean_dec(v_unused_3657_);
                    v_unused_3658_ = lean_ctor_get(v_l_3613_, 0);
                    lean_dec(v_unused_3658_);
                    v___x_3642_ = v_l_3613_;
                    v_isShared_3643_ = v_isSharedCheck_3655_;
                    state = 44;
                    continue;
                } else {
                    lean_inc(v_v_3640_);
                    lean_inc(v_k_3639_);
                    lean_dec(v_l_3613_);
                    v___x_3642_ = lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3655_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3644_ = lean_unsigned_to_nat(3);
                v___x_3645_ = lean_unsigned_to_nat(1);
                if v_isShared_3643_ == 0 {
                    lean_ctor_set(v___x_3642_, 4, v_r_3614_);
                    lean_ctor_set(v___x_3642_, 3, v_r_3614_);
                    lean_ctor_set(v___x_3642_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3642_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3642_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3642_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_r_3614_);
                    lean_ctor_set(v_reuseFailAlloc_3654_, 4, v_r_3614_);
                    v___x_3647_ = v_reuseFailAlloc_3654_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3638_ == 0 {
                    lean_ctor_set(v___x_3637_, 3, v_r_3614_);
                    lean_ctor_set(v___x_3637_, 0, v___x_3645_);
                    v___x_3649_ = v___x_3637_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3634_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3635_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_r_3614_);
                    lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_r_3614_);
                    v___x_3649_ = v_reuseFailAlloc_3653_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v___x_3649_);
                    lean_ctor_set(v___x_3335_, 3, v___x_3647_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3640_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3639_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3644_);
                    v___x_3651_ = v___x_3335_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3639_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3640_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 3, v___x_3647_);
                    lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
                    v___x_3651_ = v_reuseFailAlloc_3652_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3651_;
            }
            48 => {
                v___x_3669_ = lean_unsigned_to_nat(3);
                v___x_3670_ = lean_unsigned_to_nat(1);
                if v_isShared_3668_ == 0 {
                    lean_ctor_set(v___x_3667_, 4, v_l_3613_);
                    lean_ctor_set(v___x_3667_, 2, v_v_3331_);
                    lean_ctor_set(v___x_3667_, 1, v_k_3330_);
                    lean_ctor_set(v___x_3667_, 0, v___x_3670_);
                    v___x_3672_ = v___x_3667_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3331_);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3613_);
                    lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_l_3613_);
                    v___x_3672_ = v_reuseFailAlloc_3676_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_3336_ == 0 {
                    lean_ctor_set(v___x_3335_, 4, v_r_3663_);
                    lean_ctor_set(v___x_3335_, 3, v___x_3672_);
                    lean_ctor_set(v___x_3335_, 2, v_v_3665_);
                    lean_ctor_set(v___x_3335_, 1, v_k_3664_);
                    lean_ctor_set(v___x_3335_, 0, v___x_3669_);
                    v___x_3674_ = v___x_3335_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3669_);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3664_);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3665_);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___x_3672_);
                    lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3663_);
                    v___x_3674_ = v_reuseFailAlloc_3675_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3674_;
            }
            51 => {
                return v___x_3683_;
            }
            52 => {
                return v___x_3687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Json_setObjVal_x21___closed__2() -> *mut LeanObject {
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    v___x_3694_ = l_Lean_Json_setObjVal_x21___closed__1;
    v___x_3695_ = lean_unsigned_to_nat(21);
    v___x_3696_ = lean_unsigned_to_nat(285);
    v___x_3697_ = l_Lean_Json_setObjVal_x21___closed__0;
    v___x_3698_ =
        l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
    v___x_3699_ = l_mkPanicMessageWithDecl(
        v___x_3698_,
        v___x_3697_,
        v___x_3696_,
        v___x_3695_,
        v___x_3694_,
    );
    return v___x_3699_;
}
pub unsafe fn l_Lean_Json_setObjVal_x21(
    mut v_x_3700_: *mut LeanObject,
    mut v_x_3701_: *mut LeanObject,
    mut v_x_3702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kvPairs_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3700_) == 5 {
                    v_kvPairs_3703_ = lean_ctor_get(v_x_3700_, 0);
                    v_isSharedCheck_3711_ = (!lean_is_exclusive(v_x_3700_)) as u8;
                    if v_isSharedCheck_3711_ == 0 {
                        v___x_3705_ = v_x_3700_;
                        v_isShared_3706_ = v_isSharedCheck_3711_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_kvPairs_3703_);
                        lean_dec(v_x_3700_);
                        v___x_3705_ = lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3711_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_x_3702_);
                    lean_dec_ref(v_x_3701_);
                    lean_dec(v_x_3700_);
                    v___x_3712_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Json_setObjVal_x21___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Json_setObjVal_x21___closed__2_once),
                        _init_l_Lean_Json_setObjVal_x21___closed__2,
                    );
                    v___x_3713_ = l_panic___at___00Lean_Json_setObjVal_x21_spec__1(v___x_3712_);
                    return v___x_3713_;
                }
            }
            1 => {
                v___x_3707_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_x_3701_, v_x_3702_, v_kvPairs_3703_);
                if v_isShared_3706_ == 0 {
                    lean_ctor_set(v___x_3705_, 0, v___x_3707_);
                    v___x_3709_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
                    v___x_3709_ = v_reuseFailAlloc_3710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0(
    mut v_00_u03b2_3714_: *mut LeanObject,
    mut v_msg_3715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    v___x_3716_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(
    mut v_00_u03b2_3717_: *mut LeanObject,
    mut v_k_3718_: *mut LeanObject,
    mut v_v_3719_: *mut LeanObject,
    mut v_t_3720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    v___x_3721_ =
        l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(
            v_k_3718_, v_v_3719_, v_t_3720_,
        );
    return v___x_3721_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(
    mut v_init_3722_: *mut LeanObject,
    mut v_x_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3723_) == 0 {
                    v_k_3724_ = lean_ctor_get(v_x_3723_, 1);
                    lean_inc(v_k_3724_);
                    v_v_3725_ = lean_ctor_get(v_x_3723_, 2);
                    lean_inc(v_v_3725_);
                    v_l_3726_ = lean_ctor_get(v_x_3723_, 3);
                    lean_inc(v_l_3726_);
                    v_r_3727_ = lean_ctor_get(v_x_3723_, 4);
                    lean_inc(v_r_3727_);
                    lean_dec_ref_known(v_x_3723_, 5);
                    v___x_3728_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_3722_, v_l_3726_);
                    v___x_3729_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_3724_, v_v_3725_, v___x_3728_);
                    v_init_3722_ = v___x_3729_;
                    v_x_3723_ = v_r_3727_;
                    state = 0;
                    continue;
                } else {
                    return v_init_3722_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_mergeObj(
    mut v_x_3731_: *mut LeanObject,
    mut v_x_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kvPairs_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3731_) == 5 {
                    if lean_obj_tag(v_x_3732_) == 5 {
                        v_kvPairs_3733_ = lean_ctor_get(v_x_3731_, 0);
                        lean_inc(v_kvPairs_3733_);
                        lean_dec_ref_known(v_x_3731_, 1);
                        v_kvPairs_3734_ = lean_ctor_get(v_x_3732_, 0);
                        v_isSharedCheck_3742_ = (!lean_is_exclusive(v_x_3732_)) as u8;
                        if v_isSharedCheck_3742_ == 0 {
                            v___x_3736_ = v_x_3732_;
                            v_isShared_3737_ = v_isSharedCheck_3742_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_kvPairs_3734_);
                            lean_dec(v_x_3732_);
                            v___x_3736_ = lean_box(0);
                            v_isShared_3737_ = v_isSharedCheck_3742_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_x_3731_, 1);
                        return v_x_3732_;
                    }
                } else {
                    lean_dec(v_x_3731_);
                    return v_x_3732_;
                }
            }
            1 => {
                v___x_3738_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_3733_, v_kvPairs_3734_);
                if v_isShared_3737_ == 0 {
                    lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3740_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
                    v___x_3740_ = v_reuseFailAlloc_3741_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3740_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0(
    mut v_init_3743_: *mut LeanObject,
    mut v_t_3744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_3743_, v_t_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_Json_Structured_ctorIdx(mut v_x_3746_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_3746_) == 0 {
        let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
        v___x_3747_ = lean_unsigned_to_nat(0);
        return v___x_3747_;
    } else {
        let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
        v___x_3748_ = lean_unsigned_to_nat(1);
        return v___x_3748_;
    }
}
pub unsafe fn l_Lean_Json_Structured_ctorIdx___boxed(
    mut v_x_3749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3750_: *mut LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Lean_Json_Structured_ctorIdx(v_x_3749_);
    lean_dec_ref(v_x_3749_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Json_Structured_ctorElim___redArg(
    mut v_t_3751_: *mut LeanObject,
    mut v_k_3752_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_3751_) == 0 {
        let mut v_elems_3753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
        v_elems_3753_ = lean_ctor_get(v_t_3751_, 0);
        lean_inc_ref(v_elems_3753_);
        lean_dec_ref_known(v_t_3751_, 1);
        v___x_3754_ = lean_apply_1(v_k_3752_, v_elems_3753_);
        return v___x_3754_;
    } else {
        let mut v_kvPairs_3755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
        v_kvPairs_3755_ = lean_ctor_get(v_t_3751_, 0);
        lean_inc(v_kvPairs_3755_);
        lean_dec_ref_known(v_t_3751_, 1);
        v___x_3756_ = lean_apply_1(v_k_3752_, v_kvPairs_3755_);
        return v___x_3756_;
    }
}
pub unsafe fn l_Lean_Json_Structured_ctorElim(
    mut v_motive_3757_: *mut LeanObject,
    mut v_ctorIdx_3758_: *mut LeanObject,
    mut v_t_3759_: *mut LeanObject,
    mut v_h_3760_: *mut LeanObject,
    mut v_k_3761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3759_, v_k_3761_);
    return v___x_3762_;
}
pub unsafe fn l_Lean_Json_Structured_ctorElim___boxed(
    mut v_motive_3763_: *mut LeanObject,
    mut v_ctorIdx_3764_: *mut LeanObject,
    mut v_t_3765_: *mut LeanObject,
    mut v_h_3766_: *mut LeanObject,
    mut v_k_3767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3768_: *mut LeanObject = core::ptr::null_mut();
    v_res_3768_ = l_Lean_Json_Structured_ctorElim(
        v_motive_3763_,
        v_ctorIdx_3764_,
        v_t_3765_,
        v_h_3766_,
        v_k_3767_,
    );
    lean_dec(v_ctorIdx_3764_);
    return v_res_3768_;
}
pub unsafe fn l_Lean_Json_Structured_arr_elim___redArg(
    mut v_t_3769_: *mut LeanObject,
    mut v_arr_3770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    v___x_3771_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3769_, v_arr_3770_);
    return v___x_3771_;
}
pub unsafe fn l_Lean_Json_Structured_arr_elim(
    mut v_motive_3772_: *mut LeanObject,
    mut v_t_3773_: *mut LeanObject,
    mut v_h_3774_: *mut LeanObject,
    mut v_arr_3775_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3773_, v_arr_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Lean_Json_Structured_obj_elim___redArg(
    mut v_t_3777_: *mut LeanObject,
    mut v_obj_3778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3777_, v_obj_3778_);
    return v___x_3779_;
}
pub unsafe fn l_Lean_Json_Structured_obj_elim(
    mut v_motive_3780_: *mut LeanObject,
    mut v_t_3781_: *mut LeanObject,
    mut v_h_3782_: *mut LeanObject,
    mut v_obj_3783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    v___x_3784_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3781_, v_obj_3783_);
    return v___x_3784_;
}
pub unsafe fn l_Lean_Json_instCoeArrayStructured___lam__0(
    mut v_elems_3785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    v___x_3786_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3786_, 0, v_elems_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Json_instCoeRawStringStructured___lam__0(
    mut v_kvPairs_3789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    v___x_3790_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3790_, 0, v_kvPairs_3789_);
    return v___x_3790_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_JsonNumber_ltProp = _init_l_Lean_JsonNumber_ltProp();
    lean_mark_persistent(l_Lean_JsonNumber_ltProp);
    l_Lean_JsonNumber_instInhabited = _init_l_Lean_JsonNumber_instInhabited();
    lean_mark_persistent(l_Lean_JsonNumber_instInhabited);
    l_Lean_instInhabitedJson_default = _init_l_Lean_instInhabitedJson_default();
    lean_mark_persistent(l_Lean_instInhabitedJson_default);
    l_Lean_instInhabitedJson = _init_l_Lean_instInhabitedJson();
    lean_mark_persistent(l_Lean_instInhabitedJson);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_OfScientific(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Ord_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Substring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Json_Basic(builtin);
}
