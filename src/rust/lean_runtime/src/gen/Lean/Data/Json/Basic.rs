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
static mut l_Lean_instHashableJsonNumber_hash___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instHashableJsonNumber_hash___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instHashableJsonNumber___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instHashableJsonNumber_hash___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instHashableJsonNumber___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableJsonNumber___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instHashableJsonNumber: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instHashableJsonNumber___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instCoeNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_fromNat as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instCoeNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instCoeNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instCoeInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_fromInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instCoeInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instCoeInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instCoeInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_JsonNumber_normalize___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_normalize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_normalize___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_normalize___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_normalize___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_normalize___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_JsonNumber_ltProp: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_JsonNumber_instOrd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_instOrd___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instOrd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOrd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instOrd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOrd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_toString___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [46, 0],
    };
static mut l_Lean_JsonNumber_toString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_toString___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [101, 0],
    };
static mut l_Lean_JsonNumber_toString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_toString___closed__2_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_JsonNumber_toString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_JsonNumber_toString___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_toString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_JsonNumber_toString___closed__4_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [45, 0],
    };
static mut l_Lean_JsonNumber_toString___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_toString___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instToString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instToString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instToString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instToString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__2_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___lam__0___closed__7_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_instRepr___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instRepr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instRepr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instRepr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instOfScientific___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_JsonNumber_instOfScientific___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_JsonNumber_instOfScientific___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOfScientific___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instOfScientific: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instOfScientific___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_JsonNumber_instNeg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_JsonNumber_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instNeg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_JsonNumber_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_instNeg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_JsonNumber_instInhabited___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_instInhabited___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_JsonNumber_instInhabited: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_toFloat___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_toFloat___closed__0: f64 = 0.0;
static mut l_Lean_JsonNumber_toFloat___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_toFloat___closed__1: f64 = 0.0;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 74, 115, 111, 110, 46, 66, 97, 115, 105, 99, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value: crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 67, m_capacity: 67, m_length: 66, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 74, 115, 111, 110, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110, 46, 74, 115, 111, 110, 78, 117, 109, 98, 101, 114, 46, 102, 114, 111, 109, 80, 111, 115, 105, 116, 105, 118, 101, 70, 108, 111, 97, 116, 33, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 112, 97, 114, 115, 101, 32, 0]};
static mut l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__0: f64 = 0.0;
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__2: f64 = 0.0;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__3_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__4_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__3_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__5_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__6_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__7_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_JsonNumber_fromFloat_x3f___closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_JsonNumber_fromFloat_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_JsonNumber_fromFloat_x3f___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_instInhabitedJson_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedJson: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instBEq___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instBEq___private__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instBEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instBEq: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instBEq___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__0: u64 = 0;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__1: u64 = 0;
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2: u64 = 0;
pub static l_Lean_Json_instHashable___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instHashable___private__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instHashable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instHashable: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instHashable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instCoeNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeNat___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instCoeInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeInt___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeInt___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instCoeString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeString___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instCoeBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Json_instCoeBool___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Json_instCoeBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getObj_x3f___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Json_getObj_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getObj_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getObj_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getArr_x3f___closed__0_value: crate::leanh::LeanStringObject<15> =
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
            97, 114, 114, 97, 121, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Json_getArr_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getArr_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getArr_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getStr_x3f___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Json_getStr_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getStr_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getStr_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getStr_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getNat_x3f___closed__0_value: crate::leanh::LeanStringObject<24> =
    crate::leanh::LeanStringObject {
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
            78, 97, 116, 117, 114, 97, 108, 32, 110, 117, 109, 98, 101, 114, 32, 101, 120, 112,
            101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Json_getNat_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getNat_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getNat_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNat_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getInt_x3f___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Json_getInt_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getInt_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getInt_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getInt_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getBool_x3f___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Json_getBool_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getBool_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getBool_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getBool_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getNum_x3f___closed__0_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Json_getNum_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getNum_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getNum_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getNum_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getObjVal_x3f___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 0,
        ],
    };
static mut l_Lean_Json_getObjVal_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObjVal_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getObjVal_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getObj_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getObjVal_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getObjVal_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getArrVal_x3f___closed__0_value: crate::leanh::LeanStringObject<22> =
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
            105, 110, 100, 101, 120, 32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100,
            115, 58, 32, 0,
        ],
    };
static mut l_Lean_Json_getArrVal_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArrVal_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_getArrVal_x3f___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_Json_getArr_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Json_getArrVal_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_getArrVal_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Json_setObjVal_x21___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 74, 115, 111, 110, 46, 115, 101, 116, 79, 98, 106, 86, 97, 108,
            33, 0,
        ],
    };
static mut l_Lean_Json_setObjVal_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_setObjVal_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_setObjVal_x21___closed__1_value: crate::leanh::LeanStringObject<36> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 36,
        m_capacity: 36,
        m_length: 35,
        m_data: [
            74, 115, 111, 110, 46, 115, 101, 116, 79, 98, 106, 86, 97, 108, 33, 58, 32, 110, 111,
            116, 32, 97, 110, 32, 111, 98, 106, 101, 99, 116, 58, 32, 123, 106, 125, 0,
        ],
    };
static mut l_Lean_Json_setObjVal_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_setObjVal_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Json_setObjVal_x21___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Json_setObjVal_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Json_instCoeArrayStructured___closed__0_value: crate::leanh::LeanClosureObject<
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
    m_fun: l_Lean_Json_instCoeArrayStructured___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeArrayStructured___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeArrayStructured___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeArrayStructured: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeArrayStructured___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Json_instCoeRawStringStructured___closed__0_value:
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
    m_fun: l_Lean_Json_instCoeRawStringStructured___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Json_instCoeRawStringStructured___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeRawStringStructured___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Json_instCoeRawStringStructured: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Json_instCoeRawStringStructured___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instDecidableEqJsonNumber_decEq(
    mut v_x_1897_: *mut crate::leanh::LeanObject,
    mut v_x_1898_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_mantissa_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: u8 = 0;
    v_mantissa_1899_ = crate::leanh::lean_ctor_get(v_x_1897_, 0);
    v_exponent_1900_ = crate::leanh::lean_ctor_get(v_x_1897_, 1);
    v_mantissa_1901_ = crate::leanh::lean_ctor_get(v_x_1898_, 0);
    v_exponent_1902_ = crate::leanh::lean_ctor_get(v_x_1898_, 1);
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
    mut v_x_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1907_: u8 = 0;
    let mut v_r_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1907_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_1905_, v_x_1906_);
    crate::leanh::lean_dec_ref(v_x_1906_);
    crate::leanh::lean_dec_ref(v_x_1905_);
    v_r_1908_ = crate::leanh::lean_box((v_res_1907_) as usize);
    return v_r_1908_;
}
pub unsafe fn l_Lean_instDecidableEqJsonNumber(
    mut v_x_1909_: *mut crate::leanh::LeanObject,
    mut v_x_1910_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1911_: u8 = 0;
    v___x_1911_ = l_Lean_instDecidableEqJsonNumber_decEq(v_x_1909_, v_x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_instDecidableEqJsonNumber___boxed(
    mut v_x_1912_: *mut crate::leanh::LeanObject,
    mut v_x_1913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1914_: u8 = 0;
    let mut v_r_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1914_ = l_Lean_instDecidableEqJsonNumber(v_x_1912_, v_x_1913_);
    crate::leanh::lean_dec_ref(v_x_1913_);
    crate::leanh::lean_dec_ref(v_x_1912_);
    v_r_1915_ = crate::leanh::lean_box((v_res_1914_) as usize);
    return v_r_1915_;
}
pub unsafe fn _init_l_Lean_instHashableJsonNumber_hash___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v_natZero_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_natZero_1916_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_1917_ = lean_nat_to_int(v_natZero_1916_);
    return v_intZero_1917_;
}
pub unsafe fn l_Lean_instHashableJsonNumber_hash(
    mut v_x_1918_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_mantissa_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: u64 = 0;
    let mut v___y_1923_: u64 = 0;
    let mut v___x_1924_: u64 = 0;
    let mut v___x_1925_: u64 = 0;
    let mut v___x_1926_: u64 = 0;
    let mut v_intZero_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1928_: u8 = 0;
    let mut v_a_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: u64 = 0;
    let mut v_abs_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1919_ = crate::leanh::lean_ctor_get(v_x_1918_, 0);
                v_exponent_1920_ = crate::leanh::lean_ctor_get(v_x_1918_, 1);
                v___x_1921_ = 0u64;
                v_intZero_1927_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v_isNeg_1928_ = lean_int_dec_lt(v_mantissa_1919_, v_intZero_1927_);
                if v_isNeg_1928_ == 0 {
                    v_a_1929_ = lean_nat_abs(v_mantissa_1919_);
                    v___x_1930_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1931_ = lean_nat_mul(v___x_1930_, v_a_1929_);
                    crate::leanh::lean_dec(v_a_1929_);
                    v___x_1932_ = lean_uint64_of_nat(v___x_1931_);
                    crate::leanh::lean_dec(v___x_1931_);
                    v___y_1923_ = v___x_1932_;
                    state = 1;
                    continue;
                } else {
                    v_abs_1933_ = lean_nat_abs(v_mantissa_1919_);
                    v_one_1934_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_1935_ = lean_nat_sub(v_abs_1933_, v_one_1934_);
                    crate::leanh::lean_dec(v_abs_1933_);
                    v___x_1936_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1937_ = lean_nat_mul(v___x_1936_, v_a_1935_);
                    crate::leanh::lean_dec(v_a_1935_);
                    v___x_1938_ = lean_nat_add(v___x_1937_, v_one_1934_);
                    crate::leanh::lean_dec(v___x_1937_);
                    v___x_1939_ = lean_uint64_of_nat(v___x_1938_);
                    crate::leanh::lean_dec(v___x_1938_);
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
    mut v_x_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1941_: u64 = 0;
    let mut v_r_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1941_ = l_Lean_instHashableJsonNumber_hash(v_x_1940_);
    crate::leanh::lean_dec_ref(v_x_1940_);
    v_r_1942_ = crate::leanh::lean_box_uint64(v_res_1941_);
    return v_r_1942_;
}
pub unsafe fn l_Nat_cast___at___00Lean_JsonNumber_fromNat_spec__0(
    mut v_a_1945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = lean_nat_to_int(v_a_1945_);
    return v___x_1946_;
}
pub unsafe fn l_Lean_JsonNumber_fromNat(
    mut v_n_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = lean_nat_to_int(v_n_1947_);
    v___x_1949_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1948_);
    crate::leanh::lean_ctor_set(v___x_1950_, 1, v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_JsonNumber_fromInt(
    mut v_n_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1952_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1953_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1953_, 0, v_n_1951_);
    crate::leanh::lean_ctor_set(v___x_1953_, 1, v___x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Lean_JsonNumber_instOfNat(
    mut v_n_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = l_Lean_JsonNumber_fromNat(v_n_1958_);
    return v___x_1959_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(
    mut v_n_1960_: *mut crate::leanh::LeanObject,
    mut v_digits_1961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_1963_ = lean_nat_dec_le(v_n_1960_, v___x_1962_);
                if v___x_1963_ == 0 {
                    v___x_1964_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_1965_ = lean_nat_div(v_n_1960_, v___x_1964_);
                    crate::leanh::lean_dec(v_n_1960_);
                    v___x_1966_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1967_ = lean_nat_add(v_digits_1961_, v___x_1966_);
                    crate::leanh::lean_dec(v_digits_1961_);
                    v_n_1960_ = v___x_1965_;
                    v_digits_1961_ = v___x_1967_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_1960_);
                    return v_digits_1961_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(
    mut v_n_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1970_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1971_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits_loop(
        v_n_1969_,
        v___x_1970_,
    );
    return v___x_1971_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
    mut v_upperBound_1972_: *mut crate::leanh::LeanObject,
    mut v_a_1973_: *mut crate::leanh::LeanObject,
    mut v_b_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: u8 = 0;
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1975_ = lean_nat_dec_lt(v_a_1973_, v_upperBound_1972_);
                if v___x_1975_ == 0 {
                    crate::leanh::lean_dec(v_a_1973_);
                    return v_b_1974_;
                } else {
                    v___x_1976_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1977_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_1978_ = lean_nat_mod(v_b_1974_, v___x_1977_);
                    v___x_1979_ = lean_nat_dec_eq(v___x_1978_, v___x_1976_);
                    crate::leanh::lean_dec(v___x_1978_);
                    if v___x_1979_ == 0 {
                        crate::leanh::lean_dec(v_a_1973_);
                        return v_b_1974_;
                    } else {
                        v___x_1980_ = lean_nat_div(v_b_1974_, v___x_1977_);
                        crate::leanh::lean_dec(v_b_1974_);
                        v___x_1981_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1982_ = lean_nat_add(v_a_1973_, v___x_1981_);
                        crate::leanh::lean_dec(v_a_1973_);
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
    mut v_upperBound_1984_: *mut crate::leanh::LeanObject,
    mut v_a_1985_: *mut crate::leanh::LeanObject,
    mut v_b_1986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
        v_upperBound_1984_,
        v_a_1985_,
        v_b_1986_,
    );
    crate::leanh::lean_dec(v_upperBound_1984_);
    return v_res_1987_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1989_ = lean_nat_to_int(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1990_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
        _init_l_Lean_JsonNumber_normalize___closed__0,
    );
    v___x_1991_ = lean_int_neg(v___x_1990_);
    return v___x_1991_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1992_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
        _init_l_Lean_instHashableJsonNumber_hash___closed__0,
    );
    v___x_1993_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1994_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1994_, 0, v___x_1993_);
    crate::leanh::lean_ctor_set(v___x_1994_, 1, v___x_1992_);
    return v___x_1994_;
}
pub unsafe fn _init_l_Lean_JsonNumber_normalize___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__2),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__2_once),
        _init_l_Lean_JsonNumber_normalize___closed__2,
    );
    v___x_1996_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
        core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
        _init_l_Lean_instHashableJsonNumber_hash___closed__0,
    );
    v___x_1997_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_1996_);
    crate::leanh::lean_ctor_set(v___x_1997_, 1, v___x_1995_);
    return v___x_1997_;
}
pub unsafe fn l_Lean_JsonNumber_normalize(
    mut v_x_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mantissa_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mAbs_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nDigits_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: u8 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_1999_ = crate::leanh::lean_ctor_get(v_x_1998_, 0);
                v_exponent_2000_ = crate::leanh::lean_ctor_get(v_x_1998_, 1);
                v_isSharedCheck_2024_ = (!crate::leanh::lean_is_exclusive(v_x_1998_)) as u8;
                if v_isSharedCheck_2024_ == 0 {
                    v___x_2002_ = v_x_1998_;
                    v_isShared_2003_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exponent_2000_);
                    crate::leanh::lean_inc(v_mantissa_1999_);
                    crate::leanh::lean_dec(v_x_1998_);
                    v___x_2002_ = crate::leanh::lean_box(0);
                    v_isShared_2003_ = v_isSharedCheck_2024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2004_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2018_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2019_ = lean_int_dec_eq(v_mantissa_1999_, v___x_2018_);
                if v___x_2019_ == 0 {
                    v___x_2020_ = lean_int_dec_lt(v___x_2018_, v_mantissa_1999_);
                    if v___x_2020_ == 0 {
                        v___x_2021_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1_once),
                            _init_l_Lean_JsonNumber_normalize___closed__1,
                        );
                        v___y_2006_ = v___x_2021_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2022_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
                            _init_l_Lean_JsonNumber_normalize___closed__0,
                        );
                        v___y_2006_ = v___x_2022_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2002_);
                    crate::leanh::lean_dec(v_exponent_2000_);
                    crate::leanh::lean_dec(v_mantissa_1999_);
                    v___x_2023_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__3_once),
                        _init_l_Lean_JsonNumber_normalize___closed__3,
                    );
                    return v___x_2023_;
                }
            }
            2 => {
                v_mAbs_2007_ = lean_nat_abs(v_mantissa_1999_);
                crate::leanh::lean_dec(v_mantissa_1999_);
                crate::leanh::lean_inc(v_mAbs_2007_);
                v_nDigits_2008_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_mAbs_2007_);
                v___x_2009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(v_nDigits_2008_, v___x_2004_, v_mAbs_2007_);
                v___x_2010_ = lean_nat_to_int(v_exponent_2000_);
                v___x_2011_ = lean_int_neg(v___x_2010_);
                crate::leanh::lean_dec(v___x_2010_);
                v___x_2012_ = lean_nat_to_int(v_nDigits_2008_);
                v___x_2013_ = lean_int_add(v___x_2011_, v___x_2012_);
                crate::leanh::lean_dec(v___x_2012_);
                crate::leanh::lean_dec(v___x_2011_);
                if v_isShared_2003_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2002_, 1, v___x_2013_);
                    crate::leanh::lean_ctor_set(v___x_2002_, 0, v___x_2009_);
                    v___x_2015_ = v___x_2002_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2017_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2017_, 1, v___x_2013_);
                    v___x_2015_ = v_reuseFailAlloc_2017_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc(v___y_2006_);
                v___x_2016_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2016_, 0, v___y_2006_);
                crate::leanh::lean_ctor_set(v___x_2016_, 1, v___x_2015_);
                return v___x_2016_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(
    mut v_upperBound_2025_: *mut crate::leanh::LeanObject,
    mut v_inst_2026_: *mut crate::leanh::LeanObject,
    mut v_R_2027_: *mut crate::leanh::LeanObject,
    mut v_a_2028_: *mut crate::leanh::LeanObject,
    mut v_b_2029_: *mut crate::leanh::LeanObject,
    mut v_c_2030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___redArg(
        v_upperBound_2025_,
        v_a_2028_,
        v_b_2029_,
    );
    return v___x_2031_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0___boxed(
    mut v_upperBound_2032_: *mut crate::leanh::LeanObject,
    mut v_inst_2033_: *mut crate::leanh::LeanObject,
    mut v_R_2034_: *mut crate::leanh::LeanObject,
    mut v_a_2035_: *mut crate::leanh::LeanObject,
    mut v_b_2036_: *mut crate::leanh::LeanObject,
    mut v_c_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_JsonNumber_normalize_spec__0(
        v_upperBound_2032_,
        v_inst_2033_,
        v_R_2034_,
        v_a_2035_,
        v_b_2036_,
        v_c_2037_,
    );
    crate::leanh::lean_dec(v_upperBound_2032_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_JsonNumber_lt(
    mut v_a_2039_: *mut crate::leanh::LeanObject,
    mut v_b_2040_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___y_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2043_: u8 = 0;
    let mut v___y_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: u8 = 0;
    let mut v_fst_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_amDigits_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bmDigits_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: u8 = 0;
    let mut v___x_2059_: u8 = 0;
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2075_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: u8 = 0;
    let mut v___x_2079_: u8 = 0;
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: u8 = 0;
    let mut v___x_2083_: u8 = 0;
    let mut v___x_2084_: u8 = 0;
    let mut v___x_2085_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2068_ = l_Lean_JsonNumber_normalize(v_a_2039_);
                v_fst_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                crate::leanh::lean_inc(v_fst_2069_);
                v_snd_2070_ = crate::leanh::lean_ctor_get(v___x_2068_, 1);
                crate::leanh::lean_inc(v_snd_2070_);
                crate::leanh::lean_dec_ref(v___x_2068_);
                v___x_2071_ = l_Lean_JsonNumber_normalize(v_b_2040_);
                v_fst_2072_ = crate::leanh::lean_ctor_get(v___x_2071_, 0);
                crate::leanh::lean_inc(v_fst_2072_);
                v_snd_2073_ = crate::leanh::lean_ctor_get(v___x_2071_, 1);
                crate::leanh::lean_inc(v_snd_2073_);
                crate::leanh::lean_dec_ref(v___x_2071_);
                v___x_2080_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__0_once),
                    _init_l_Lean_JsonNumber_normalize___closed__0,
                );
                v___x_2081_ = crate::leanh::lean_obj_once(
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
                            crate::leanh::lean_dec(v_snd_2073_);
                            crate::leanh::lean_dec(v_fst_2072_);
                            crate::leanh::lean_dec(v_snd_2070_);
                            crate::leanh::lean_dec(v_fst_2069_);
                            return v___x_2082_;
                        }
                    }
                } else {
                    v___x_2085_ = lean_int_dec_eq(v_fst_2072_, v___x_2080_);
                    if v___x_2085_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_2073_);
                        crate::leanh::lean_dec(v_fst_2072_);
                        crate::leanh::lean_dec(v_snd_2070_);
                        crate::leanh::lean_dec(v_fst_2069_);
                        return v___x_2085_;
                    }
                }
            }
            1 => {
                if v___y_2043_ == 0 {
                    v___x_2047_ = lean_int_dec_lt(v___y_2042_, v___y_2044_);
                    crate::leanh::lean_dec(v___y_2044_);
                    crate::leanh::lean_dec(v___y_2042_);
                    if v___x_2047_ == 0 {
                        v___x_2048_ = lean_nat_dec_lt(v_fst_2045_, v_snd_2046_);
                        crate::leanh::lean_dec(v_snd_2046_);
                        crate::leanh::lean_dec(v_fst_2045_);
                        return v___x_2048_;
                    } else {
                        crate::leanh::lean_dec(v_snd_2046_);
                        crate::leanh::lean_dec(v_fst_2045_);
                        return v___y_2043_;
                    }
                } else {
                    crate::leanh::lean_dec(v_snd_2046_);
                    crate::leanh::lean_dec(v_fst_2045_);
                    crate::leanh::lean_dec(v___y_2044_);
                    crate::leanh::lean_dec(v___y_2042_);
                    return v___y_2043_;
                }
            }
            2 => {
                v_fst_2052_ = crate::leanh::lean_ctor_get(v_fst_2050_, 0);
                crate::leanh::lean_inc_n(v_fst_2052_, 2);
                v_snd_2053_ = crate::leanh::lean_ctor_get(v_fst_2050_, 1);
                crate::leanh::lean_inc(v_snd_2053_);
                crate::leanh::lean_dec_ref(v_fst_2050_);
                v_fst_2054_ = crate::leanh::lean_ctor_get(v_snd_2051_, 0);
                crate::leanh::lean_inc_n(v_fst_2054_, 2);
                v_snd_2055_ = crate::leanh::lean_ctor_get(v_snd_2051_, 1);
                crate::leanh::lean_inc(v_snd_2055_);
                crate::leanh::lean_dec_ref(v_snd_2051_);
                v_amDigits_2056_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_2052_);
                v_bmDigits_2057_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_fst_2054_);
                v___x_2058_ = lean_int_dec_lt(v_snd_2053_, v_snd_2055_);
                v___x_2059_ = lean_nat_dec_lt(v_amDigits_2056_, v_bmDigits_2057_);
                if v___x_2059_ == 0 {
                    v___x_2060_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_2061_ = lean_nat_sub(v_amDigits_2056_, v_bmDigits_2057_);
                    crate::leanh::lean_dec(v_bmDigits_2057_);
                    crate::leanh::lean_dec(v_amDigits_2056_);
                    v___x_2062_ = lean_nat_pow(v___x_2060_, v___x_2061_);
                    crate::leanh::lean_dec(v___x_2061_);
                    v___x_2063_ = lean_nat_mul(v_fst_2054_, v___x_2062_);
                    crate::leanh::lean_dec(v___x_2062_);
                    crate::leanh::lean_dec(v_fst_2054_);
                    v___y_2042_ = v_snd_2055_;
                    v___y_2043_ = v___x_2058_;
                    v___y_2044_ = v_snd_2053_;
                    v_fst_2045_ = v_fst_2052_;
                    v_snd_2046_ = v___x_2063_;
                    state = 1;
                    continue;
                } else {
                    v___x_2064_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_2065_ = lean_nat_sub(v_bmDigits_2057_, v_amDigits_2056_);
                    crate::leanh::lean_dec(v_amDigits_2056_);
                    crate::leanh::lean_dec(v_bmDigits_2057_);
                    v___x_2066_ = lean_nat_pow(v___x_2064_, v___x_2065_);
                    crate::leanh::lean_dec(v___x_2065_);
                    v___x_2067_ = lean_nat_mul(v_fst_2052_, v___x_2066_);
                    crate::leanh::lean_dec(v___x_2066_);
                    crate::leanh::lean_dec(v_fst_2052_);
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
                v___x_2077_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_normalize___closed__1_once),
                    _init_l_Lean_JsonNumber_normalize___closed__1,
                );
                v___x_2078_ = lean_int_dec_eq(v_fst_2069_, v___x_2077_);
                crate::leanh::lean_dec(v_fst_2069_);
                if v___x_2078_ == 0 {
                    crate::leanh::lean_dec(v_fst_2072_);
                    v___y_2075_ = v___x_2078_;
                    state = 3;
                    continue;
                } else {
                    v___x_2079_ = lean_int_dec_eq(v_fst_2072_, v___x_2077_);
                    crate::leanh::lean_dec(v_fst_2072_);
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
    mut v_a_2086_: *mut crate::leanh::LeanObject,
    mut v_b_2087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2088_: u8 = 0;
    let mut v_r_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2088_ = l_Lean_JsonNumber_lt(v_a_2086_, v_b_2087_);
    v_r_2089_ = crate::leanh::lean_box((v_res_2088_) as usize);
    return v_r_2089_;
}
pub unsafe fn _init_l_Lean_JsonNumber_ltProp() -> *mut crate::leanh::LeanObject {
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ = crate::leanh::lean_box(0);
    return v___x_2090_;
}
pub unsafe fn l_Lean_JsonNumber_instDecidableLt(
    mut v_a_2091_: *mut crate::leanh::LeanObject,
    mut v_b_2092_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2093_: u8 = 0;
    v___x_2093_ = l_Lean_JsonNumber_lt(v_a_2091_, v_b_2092_);
    return v___x_2093_;
}
pub unsafe fn l_Lean_JsonNumber_instDecidableLt___boxed(
    mut v_a_2094_: *mut crate::leanh::LeanObject,
    mut v_b_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2096_: u8 = 0;
    let mut v_r_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2096_ = l_Lean_JsonNumber_instDecidableLt(v_a_2094_, v_b_2095_);
    v_r_2097_ = crate::leanh::lean_box((v_res_2096_) as usize);
    return v_r_2097_;
}
pub unsafe fn l_Lean_JsonNumber_instOrd___lam__0(
    mut v_x_2098_: *mut crate::leanh::LeanObject,
    mut v_y_2099_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2100_: u8 = 0;
    crate::leanh::lean_inc_ref(v_y_2099_);
    crate::leanh::lean_inc_ref(v_x_2098_);
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
        crate::leanh::lean_dec_ref(v_y_2099_);
        crate::leanh::lean_dec_ref(v_x_2098_);
        v___x_2104_ = 0;
        return v___x_2104_;
    }
}
pub unsafe fn l_Lean_JsonNumber_instOrd___lam__0___boxed(
    mut v_x_2105_: *mut crate::leanh::LeanObject,
    mut v_y_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2107_: u8 = 0;
    let mut v_r_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2107_ = l_Lean_JsonNumber_instOrd___lam__0(v_x_2105_, v_y_2106_);
    v_r_2108_ = crate::leanh::lean_box((v_res_2107_) as usize);
    return v_r_2108_;
}
pub unsafe fn l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
    mut v_s_2111_: *mut crate::leanh::LeanObject,
    mut v_begPos_2112_: *mut crate::leanh::LeanObject,
    mut v_i_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2114_: u8 = 0;
    let mut v_i_x27_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                        crate::leanh::lean_dec(v_i_x27_2115_);
                        return v_i_2113_;
                    } else {
                        crate::leanh::lean_dec(v_i_2113_);
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
    mut v_s_2120_: *mut crate::leanh::LeanObject,
    mut v_begPos_2121_: *mut crate::leanh::LeanObject,
    mut v_i_2122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2123_ = l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
        v_s_2120_,
        v_begPos_2121_,
        v_i_2122_,
    );
    crate::leanh::lean_dec(v_begPos_2121_);
    crate::leanh::lean_dec_ref(v_s_2120_);
    return v_res_2123_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toString___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2127_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_2128_ = lean_nat_to_int(v___x_2127_);
    return v___x_2128_;
}
pub unsafe fn l_Lean_JsonNumber_toString(
    mut v_x_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: u8 = 0;
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2151_: u8 = 0;
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_right_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_left_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: u8 = 0;
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: u8 = 0;
    let mut v___y_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exp_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: u8 = 0;
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2141_ = crate::leanh::lean_ctor_get(v_x_2130_, 0);
                crate::leanh::lean_inc(v_mantissa_2141_);
                v_exponent_2142_ = crate::leanh::lean_ctor_get(v_x_2130_, 1);
                crate::leanh::lean_inc(v_exponent_2142_);
                crate::leanh::lean_dec_ref(v_x_2130_);
                v___x_2143_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2165_ = lean_nat_dec_eq(v_exponent_2142_, v___x_2143_);
                if v___x_2165_ == 0 {
                    v___x_2166_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_dec(v_exponent_2142_);
                    v___x_2193_ = l_Int_repr(v_mantissa_2141_);
                    crate::leanh::lean_dec(v_mantissa_2141_);
                    return v___x_2193_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2132_);
                v___x_2136_ = lean_string_append(v___y_2132_, v___y_2133_);
                crate::leanh::lean_dec_ref(v___y_2133_);
                v___x_2137_ = l_Lean_JsonNumber_toString___closed__0;
                v___x_2138_ = lean_string_append(v___x_2136_, v___x_2137_);
                v___x_2139_ = lean_string_append(v___x_2138_, v___y_2134_);
                crate::leanh::lean_dec_ref(v___y_2134_);
                v___x_2140_ = lean_string_append(v___x_2139_, v___y_2135_);
                crate::leanh::lean_dec_ref(v___y_2135_);
                return v___x_2140_;
            }
            2 => {
                if v___y_2151_ == 0 {
                    v___x_2152_ = lean_nat_add(v___y_2148_, v___y_2150_);
                    crate::leanh::lean_dec(v___y_2150_);
                    crate::leanh::lean_dec(v___y_2148_);
                    v___x_2153_ = l_Nat_reprFast(v___x_2152_);
                    v___x_2154_ = lean_string_utf8_byte_size(v___x_2153_);
                    crate::leanh::lean_inc_ref(v___x_2153_);
                    v___x_2155_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2155_, 0, v___x_2153_);
                    crate::leanh::lean_ctor_set(v___x_2155_, 1, v___x_2143_);
                    crate::leanh::lean_ctor_set(v___x_2155_, 2, v___x_2154_);
                    v___x_2156_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2157_ = l_Substring_Raw_nextn(v___x_2155_, v___x_2156_, v___x_2143_);
                    crate::leanh::lean_dec_ref_known(v___x_2155_, 3);
                    v_e_2158_ =
                        l_Substring_Raw_takeRightWhileAux___at___00Lean_JsonNumber_toString_spec__0(
                            v___x_2153_,
                            v___x_2157_,
                            v___x_2154_,
                        );
                    v_right_2159_ = lean_string_utf8_extract(v___x_2153_, v___x_2157_, v_e_2158_);
                    crate::leanh::lean_dec(v_e_2158_);
                    crate::leanh::lean_dec(v___x_2157_);
                    crate::leanh::lean_dec_ref(v___x_2153_);
                    if v___y_2145_ == 0 {
                        v___x_2160_ = l_Lean_JsonNumber_toString___closed__1;
                        v___x_2161_ = l_Int_repr(v___y_2149_);
                        crate::leanh::lean_dec(v___y_2149_);
                        v___x_2162_ = lean_string_append(v___x_2160_, v___x_2161_);
                        crate::leanh::lean_dec_ref(v___x_2161_);
                        v___y_2132_ = v___y_2146_;
                        v___y_2133_ = v___y_2147_;
                        v___y_2134_ = v_right_2159_;
                        v___y_2135_ = v___x_2162_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_2149_);
                        v___x_2163_ = l_Lean_JsonNumber_toString___closed__2;
                        v___y_2132_ = v___y_2146_;
                        v___y_2133_ = v___y_2147_;
                        v___y_2134_ = v_right_2159_;
                        v___y_2135_ = v___x_2163_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2150_);
                    crate::leanh::lean_dec(v___y_2149_);
                    crate::leanh::lean_dec(v___y_2148_);
                    crate::leanh::lean_inc_ref(v___y_2146_);
                    v___x_2164_ = lean_string_append(v___y_2146_, v___y_2147_);
                    crate::leanh::lean_dec_ref(v___y_2147_);
                    return v___x_2164_;
                }
            }
            3 => {
                v___x_2171_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_2172_ = lean_nat_abs(v___y_2170_);
                v___x_2173_ = lean_nat_sub(v_exponent_2142_, v___x_2172_);
                crate::leanh::lean_dec(v___x_2172_);
                crate::leanh::lean_dec(v_exponent_2142_);
                v_e_x27_2174_ = lean_nat_pow(v___x_2171_, v___x_2173_);
                crate::leanh::lean_dec(v___x_2173_);
                v___x_2175_ = lean_nat_div(v___y_2169_, v_e_x27_2174_);
                v_left_2176_ = l_Nat_reprFast(v___x_2175_);
                v___x_2177_ = lean_int_dec_eq(v___y_2170_, v___x_2166_);
                v___x_2178_ = lean_nat_mod(v___y_2169_, v_e_x27_2174_);
                crate::leanh::lean_dec(v___y_2169_);
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
                crate::leanh::lean_dec(v_mantissa_2141_);
                v___x_2183_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_toString___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_toString___closed__3_once),
                    _init_l_Lean_JsonNumber_toString___closed__3,
                );
                crate::leanh::lean_inc(v_m_2182_);
                v___x_2184_ =
                    l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_countDigits(v_m_2182_);
                v___x_2185_ = lean_nat_to_int(v___x_2184_);
                v___x_2186_ = lean_int_add(v___x_2183_, v___x_2185_);
                crate::leanh::lean_dec(v___x_2185_);
                crate::leanh::lean_inc(v_exponent_2142_);
                v___x_2187_ = lean_nat_to_int(v_exponent_2142_);
                v_exp_2188_ = lean_int_sub(v___x_2186_, v___x_2187_);
                crate::leanh::lean_dec(v___x_2187_);
                crate::leanh::lean_dec(v___x_2186_);
                v___x_2189_ = lean_int_dec_lt(v_exp_2188_, v___x_2166_);
                if v___x_2189_ == 0 {
                    crate::leanh::lean_dec(v_exp_2188_);
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
    mut v_x_2194_: *mut crate::leanh::LeanObject,
    mut v_x_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mantissa_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2210_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2196_ = crate::leanh::lean_ctor_get(v_x_2194_, 0);
                v_exponent_2197_ = crate::leanh::lean_ctor_get(v_x_2194_, 1);
                v_isSharedCheck_2210_ = (!crate::leanh::lean_is_exclusive(v_x_2194_)) as u8;
                if v_isSharedCheck_2210_ == 0 {
                    v___x_2199_ = v_x_2194_;
                    v_isShared_2200_ = v_isSharedCheck_2210_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exponent_2197_);
                    crate::leanh::lean_inc(v_mantissa_2196_);
                    crate::leanh::lean_dec(v_x_2194_);
                    v___x_2199_ = crate::leanh::lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2210_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_2202_ = lean_nat_sub(v_x_2195_, v_exponent_2197_);
                v___x_2203_ = lean_nat_pow(v___x_2201_, v___x_2202_);
                crate::leanh::lean_dec(v___x_2202_);
                v___x_2204_ = lean_nat_to_int(v___x_2203_);
                v___x_2205_ = lean_int_mul(v_mantissa_2196_, v___x_2204_);
                crate::leanh::lean_dec(v___x_2204_);
                crate::leanh::lean_dec(v_mantissa_2196_);
                v___x_2206_ = lean_nat_sub(v_exponent_2197_, v_x_2195_);
                crate::leanh::lean_dec(v_exponent_2197_);
                if v_isShared_2200_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2199_, 1, v___x_2206_);
                    crate::leanh::lean_ctor_set(v___x_2199_, 0, v___x_2205_);
                    v___x_2208_ = v___x_2199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2209_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2205_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2206_);
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
    mut v_x_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2213_ = l_Lean_JsonNumber_shiftl(v_x_2211_, v_x_2212_);
    crate::leanh::lean_dec(v_x_2212_);
    return v_res_2213_;
}
pub unsafe fn l_Lean_JsonNumber_shiftr(
    mut v_x_2214_: *mut crate::leanh::LeanObject,
    mut v_x_2215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mantissa_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2220_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2216_ = crate::leanh::lean_ctor_get(v_x_2214_, 0);
                v_exponent_2217_ = crate::leanh::lean_ctor_get(v_x_2214_, 1);
                v_isSharedCheck_2225_ = (!crate::leanh::lean_is_exclusive(v_x_2214_)) as u8;
                if v_isSharedCheck_2225_ == 0 {
                    v___x_2219_ = v_x_2214_;
                    v_isShared_2220_ = v_isSharedCheck_2225_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exponent_2217_);
                    crate::leanh::lean_inc(v_mantissa_2216_);
                    crate::leanh::lean_dec(v_x_2214_);
                    v___x_2219_ = crate::leanh::lean_box(0);
                    v_isShared_2220_ = v_isSharedCheck_2225_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2221_ = lean_nat_add(v_exponent_2217_, v_x_2215_);
                crate::leanh::lean_dec(v_exponent_2217_);
                if v_isShared_2220_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2219_, 1, v___x_2221_);
                    v___x_2223_ = v___x_2219_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_mantissa_2216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 1, v___x_2221_);
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
    mut v_x_2226_: *mut crate::leanh::LeanObject,
    mut v_x_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_JsonNumber_shiftr(v_x_2226_, v_x_2227_);
    crate::leanh::lean_dec(v_x_2227_);
    return v_res_2228_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lean_JsonNumber_instRepr___lam__0___closed__0;
    v___x_2237_ = lean_string_length(v___x_2236_);
    return v___x_2237_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2238_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__4),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__4_once),
        _init_l_Lean_JsonNumber_instRepr___lam__0___closed__4,
    );
    v___x_2239_ = lean_nat_to_int(v___x_2238_);
    return v___x_2239_;
}
pub unsafe fn l_Lean_JsonNumber_instRepr___lam__0(
    mut v_x_2244_: *mut crate::leanh::LeanObject,
    mut v_x_2245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mantissa_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2246_ = crate::leanh::lean_ctor_get(v_x_2244_, 0);
                v_exponent_2247_ = crate::leanh::lean_ctor_get(v_x_2244_, 1);
                v_isSharedCheck_2276_ = (!crate::leanh::lean_is_exclusive(v_x_2244_)) as u8;
                if v_isSharedCheck_2276_ == 0 {
                    v___x_2249_ = v_x_2244_;
                    v_isShared_2250_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exponent_2247_);
                    crate::leanh::lean_inc(v_mantissa_2246_);
                    crate::leanh::lean_dec(v_x_2244_);
                    v___x_2249_ = crate::leanh::lean_box(0);
                    v_isShared_2250_ = v_isSharedCheck_2276_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2268_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2269_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2270_ = lean_int_dec_lt(v_mantissa_2246_, v___x_2269_);
                if v___x_2270_ == 0 {
                    v___x_2271_ = l_Int_repr(v_mantissa_2246_);
                    crate::leanh::lean_dec(v_mantissa_2246_);
                    v___x_2272_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2272_, 0, v___x_2271_);
                    v___y_2252_ = v___x_2272_;
                    state = 2;
                    continue;
                } else {
                    v___x_2273_ = l_Int_repr(v_mantissa_2246_);
                    crate::leanh::lean_dec(v_mantissa_2246_);
                    v___x_2274_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2274_, 0, v___x_2273_);
                    v___x_2275_ = l_Repr_addAppParen(v___x_2274_, v___x_2268_);
                    v___y_2252_ = v___x_2275_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2253_ = l_Lean_JsonNumber_instRepr___lam__0___closed__2;
                if v_isShared_2250_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2249_, 5);
                    crate::leanh::lean_ctor_set(v___x_2249_, 1, v___x_2253_);
                    crate::leanh::lean_ctor_set(v___x_2249_, 0, v___y_2252_);
                    v___x_2255_ = v___x_2249_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___y_2252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2267_, 1, v___x_2253_);
                    v___x_2255_ = v_reuseFailAlloc_2267_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2256_ = l_Nat_reprFast(v_exponent_2247_);
                v___x_2257_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2257_, 0, v___x_2256_);
                v___x_2258_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2255_);
                crate::leanh::lean_ctor_set(v___x_2258_, 1, v___x_2257_);
                v___x_2259_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_JsonNumber_instRepr___lam__0___closed__5_once),
                    _init_l_Lean_JsonNumber_instRepr___lam__0___closed__5,
                );
                v___x_2260_ = l_Lean_JsonNumber_instRepr___lam__0___closed__6;
                v___x_2261_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2261_, 0, v___x_2260_);
                crate::leanh::lean_ctor_set(v___x_2261_, 1, v___x_2258_);
                v___x_2262_ = l_Lean_JsonNumber_instRepr___lam__0___closed__7;
                v___x_2263_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2263_, 0, v___x_2261_);
                crate::leanh::lean_ctor_set(v___x_2263_, 1, v___x_2262_);
                v___x_2264_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2259_);
                crate::leanh::lean_ctor_set(v___x_2264_, 1, v___x_2263_);
                v___x_2265_ = 0;
                v___x_2266_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2266_, 0, v___x_2264_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2266_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2265_,
                );
                return v___x_2266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_instRepr___lam__0___boxed(
    mut v_x_2277_: *mut crate::leanh::LeanObject,
    mut v_x_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2279_ = l_Lean_JsonNumber_instRepr___lam__0(v_x_2277_, v_x_2278_);
    crate::leanh::lean_dec(v_x_2278_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_JsonNumber_instOfScientific___lam__0(
    mut v_mantissa_2282_: *mut crate::leanh::LeanObject,
    mut v_exponentSign_2283_: u8,
    mut v_decimalExponent_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_exponentSign_2283_ == 0 {
        let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2285_ = crate::leanh::lean_unsigned_to_nat(10);
        v___x_2286_ = lean_nat_pow(v___x_2285_, v_decimalExponent_2284_);
        crate::leanh::lean_dec(v_decimalExponent_2284_);
        v___x_2287_ = lean_nat_mul(v_mantissa_2282_, v___x_2286_);
        crate::leanh::lean_dec(v___x_2286_);
        crate::leanh::lean_dec(v_mantissa_2282_);
        v___x_2288_ = lean_nat_to_int(v___x_2287_);
        v___x_2289_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2290_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2290_, 0, v___x_2288_);
        crate::leanh::lean_ctor_set(v___x_2290_, 1, v___x_2289_);
        return v___x_2290_;
    } else {
        let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2291_ = lean_nat_to_int(v_mantissa_2282_);
        v___x_2292_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2292_, 0, v___x_2291_);
        crate::leanh::lean_ctor_set(v___x_2292_, 1, v_decimalExponent_2284_);
        return v___x_2292_;
    }
}
pub unsafe fn l_Lean_JsonNumber_instOfScientific___lam__0___boxed(
    mut v_mantissa_2293_: *mut crate::leanh::LeanObject,
    mut v_exponentSign_2294_: *mut crate::leanh::LeanObject,
    mut v_decimalExponent_2295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exponentSign_boxed_2296_: u8 = 0;
    let mut v_res_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_exponentSign_boxed_2296_ = (crate::leanh::lean_unbox(v_exponentSign_2294_) as u8);
    v_res_2297_ = l_Lean_JsonNumber_instOfScientific___lam__0(
        v_mantissa_2293_,
        v_exponentSign_boxed_2296_,
        v_decimalExponent_2295_,
    );
    return v_res_2297_;
}
pub unsafe fn l_Lean_JsonNumber_instNeg___lam__0(
    mut v_jn_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_mantissa_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2301_ = crate::leanh::lean_ctor_get(v_jn_2300_, 0);
                v_exponent_2302_ = crate::leanh::lean_ctor_get(v_jn_2300_, 1);
                v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v_jn_2300_)) as u8;
                if v_isSharedCheck_2310_ == 0 {
                    v___x_2304_ = v_jn_2300_;
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exponent_2302_);
                    crate::leanh::lean_inc(v_mantissa_2301_);
                    crate::leanh::lean_dec(v_jn_2300_);
                    v___x_2304_ = crate::leanh::lean_box(0);
                    v_isShared_2305_ = v_isSharedCheck_2310_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2306_ = lean_int_neg(v_mantissa_2301_);
                crate::leanh::lean_dec(v_mantissa_2301_);
                if v_isShared_2305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2306_);
                    v___x_2308_ = v___x_2304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v___x_2306_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_exponent_2302_);
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
pub unsafe fn _init_l_Lean_JsonNumber_instInhabited___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2313_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2314_ = l_Lean_JsonNumber_fromNat(v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn _init_l_Lean_JsonNumber_instInhabited() -> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0_once),
        _init_l_Lean_JsonNumber_instInhabited___closed__0,
    );
    return v___x_2315_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toFloat___closed__0() -> f64 {
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: f64 = 0.0;
    v___x_2316_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2317_ = 1;
    v___x_2318_ = crate::leanh::lean_unsigned_to_nat(10);
    v___x_2319_ = l_Float_ofScientific(v___x_2318_, v___x_2317_, v___x_2316_);
    return v___x_2319_;
}
pub unsafe fn _init_l_Lean_JsonNumber_toFloat___closed__1() -> f64 {
    let mut v___x_2320_: f64 = 0.0;
    let mut v___x_2321_: f64 = 0.0;
    v___x_2320_ = crate::leanh::lean_float_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__0_once),
        _init_l_Lean_JsonNumber_toFloat___closed__0,
    );
    v___x_2321_ = lean_float_negate(v___x_2320_);
    return v___x_2321_;
}
pub unsafe fn l_Lean_JsonNumber_toFloat(mut v_x_2322_: *mut crate::leanh::LeanObject) -> f64 {
    let mut v_mantissa_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2326_: f64 = 0.0;
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: u8 = 0;
    let mut v___x_2329_: f64 = 0.0;
    let mut v___x_2330_: f64 = 0.0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u8 = 0;
    let mut v___x_2333_: f64 = 0.0;
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: f64 = 0.0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mantissa_2323_ = crate::leanh::lean_ctor_get(v_x_2322_, 0);
                crate::leanh::lean_inc(v_mantissa_2323_);
                v_exponent_2324_ = crate::leanh::lean_ctor_get(v_x_2322_, 1);
                crate::leanh::lean_inc(v_exponent_2324_);
                crate::leanh::lean_dec_ref(v_x_2322_);
                v___x_2331_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v___x_2332_ = lean_int_dec_le(v___x_2331_, v_mantissa_2323_);
                if v___x_2332_ == 0 {
                    v___x_2333_ = crate::leanh::lean_float_once(
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_JsonNumber_toFloat___closed__1_once),
                        _init_l_Lean_JsonNumber_toFloat___closed__1,
                    );
                    v___y_2326_ = v___x_2333_;
                    state = 1;
                    continue;
                } else {
                    v___x_2334_ = crate::leanh::lean_unsigned_to_nat(10);
                    v___x_2335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2336_ = l_Float_ofScientific(v___x_2334_, v___x_2332_, v___x_2335_);
                    v___y_2326_ = v___x_2336_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2327_ = lean_nat_abs(v_mantissa_2323_);
                crate::leanh::lean_dec(v_mantissa_2323_);
                v___x_2328_ = 1;
                v___x_2329_ = l_Float_ofScientific(v___x_2327_, v___x_2328_, v_exponent_2324_);
                crate::leanh::lean_dec(v___x_2327_);
                v___x_2330_ = lean_float_mul(v___y_2326_, v___x_2329_);
                return v___x_2330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_toFloat___boxed(
    mut v_x_2337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2338_: f64 = 0.0;
    let mut v_r_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2338_ = l_Lean_JsonNumber_toFloat(v_x_2337_);
    v_r_2339_ = crate::leanh::lean_box_float(v_res_2338_);
    return v_r_2339_;
}
pub unsafe fn l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(
    mut v_msg_2340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Lean_JsonNumber_instInhabited;
    v___x_2342_ = lean_panic_fn_borrowed(v___x_2341_, v_msg_2340_);
    return v___x_2342_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(
    mut v_x_2346_: f64,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: u8 = 0;
    let mut v_fst_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_unused_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2380_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2385_: u8 = 0;
    let mut v_unused_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2347_ = lean_float_to_string(v_x_2346_);
                v___x_2348_ = l_Lean_Syntax_decodeScientificLitVal_x3f(v___x_2347_);
                if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                    v___x_2349_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__0;
                    v___x_2350_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__1;
                    v___x_2351_ = crate::leanh::lean_unsigned_to_nat(160);
                    v___x_2352_ = crate::leanh::lean_unsigned_to_nat(12);
                    v___x_2353_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21___closed__2;
                    v___x_2354_ = lean_string_append(v___x_2353_, v___x_2347_);
                    crate::leanh::lean_dec_ref(v___x_2347_);
                    v___x_2355_ = l_mkPanicMessageWithDecl(
                        v___x_2349_,
                        v___x_2350_,
                        v___x_2351_,
                        v___x_2352_,
                        v___x_2354_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2354_);
                    v___x_2356_ = l_panic___at___00__private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21_spec__0(v___x_2355_);
                    return v___x_2356_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2347_);
                    v_val_2357_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    crate::leanh::lean_inc(v_val_2357_);
                    crate::leanh::lean_dec_ref_known(v___x_2348_, 1);
                    v_snd_2358_ = crate::leanh::lean_ctor_get(v_val_2357_, 1);
                    crate::leanh::lean_inc(v_snd_2358_);
                    v_fst_2359_ = crate::leanh::lean_ctor_get(v_snd_2358_, 0);
                    v___x_2360_ = (crate::leanh::lean_unbox(v_fst_2359_) as u8);
                    if v___x_2360_ == 0 {
                        v_fst_2361_ = crate::leanh::lean_ctor_get(v_val_2357_, 0);
                        crate::leanh::lean_inc(v_fst_2361_);
                        crate::leanh::lean_dec(v_val_2357_);
                        v_snd_2362_ = crate::leanh::lean_ctor_get(v_snd_2358_, 1);
                        v_isSharedCheck_2374_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_2358_)) as u8;
                        if v_isSharedCheck_2374_ == 0 {
                            v_unused_2375_ = crate::leanh::lean_ctor_get(v_snd_2358_, 0);
                            crate::leanh::lean_dec(v_unused_2375_);
                            v___x_2364_ = v_snd_2358_;
                            v_isShared_2365_ = v_isSharedCheck_2374_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2362_);
                            crate::leanh::lean_dec(v_snd_2358_);
                            v___x_2364_ = crate::leanh::lean_box(0);
                            v_isShared_2365_ = v_isSharedCheck_2374_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_fst_2376_ = crate::leanh::lean_ctor_get(v_val_2357_, 0);
                        crate::leanh::lean_inc(v_fst_2376_);
                        crate::leanh::lean_dec(v_val_2357_);
                        v_snd_2377_ = crate::leanh::lean_ctor_get(v_snd_2358_, 1);
                        v_isSharedCheck_2385_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_2358_)) as u8;
                        if v_isSharedCheck_2385_ == 0 {
                            v_unused_2386_ = crate::leanh::lean_ctor_get(v_snd_2358_, 0);
                            crate::leanh::lean_dec(v_unused_2386_);
                            v___x_2379_ = v_snd_2358_;
                            v_isShared_2380_ = v_isSharedCheck_2385_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_2377_);
                            crate::leanh::lean_dec(v_snd_2358_);
                            v___x_2379_ = crate::leanh::lean_box(0);
                            v_isShared_2380_ = v_isSharedCheck_2385_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2366_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_2367_ = lean_nat_pow(v___x_2366_, v_snd_2362_);
                crate::leanh::lean_dec(v_snd_2362_);
                v___x_2368_ = lean_nat_mul(v_fst_2361_, v___x_2367_);
                crate::leanh::lean_dec(v___x_2367_);
                crate::leanh::lean_dec(v_fst_2361_);
                v___x_2369_ = lean_nat_to_int(v___x_2368_);
                v___x_2370_ = crate::leanh::lean_unsigned_to_nat(0);
                if v_isShared_2365_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2364_, 1, v___x_2370_);
                    crate::leanh::lean_ctor_set(v___x_2364_, 0, v___x_2369_);
                    v___x_2372_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2370_);
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
                    crate::leanh::lean_ctor_set(v___x_2379_, 0, v___x_2381_);
                    v___x_2383_ = v___x_2379_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2384_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2381_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_snd_2377_);
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
    mut v_x_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2388_: f64 = 0.0;
    let mut v_res_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2388_ = crate::leanh::lean_unbox_float(v_x_2387_);
    crate::leanh::lean_dec_ref(v_x_2387_);
    v_res_2389_ =
        l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v_x_boxed_2388_);
    return v_res_2389_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__0() -> f64 {
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: u8 = 0;
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: f64 = 0.0;
    v___x_2390_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2391_ = 1;
    v___x_2392_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2393_ = l_Float_ofScientific(v___x_2392_, v___x_2391_, v___x_2390_);
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2394_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0),
        core::ptr::addr_of_mut!(l_Lean_JsonNumber_instInhabited___closed__0_once),
        _init_l_Lean_JsonNumber_instInhabited___closed__0,
    );
    v___x_2395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2395_, 0, v___x_2394_);
    return v___x_2395_;
}
pub unsafe fn _init_l_Lean_JsonNumber_fromFloat_x3f___closed__2() -> f64 {
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: f64 = 0.0;
    v___x_2396_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2397_ = lean_float_of_nat(v___x_2396_);
    return v___x_2397_;
}
pub unsafe fn l_Lean_JsonNumber_fromFloat_x3f(mut v_x_2407_: f64) -> *mut crate::leanh::LeanObject {
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: f64 = 0.0;
    let mut v___x_2411_: u8 = 0;
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: f64 = 0.0;
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mantissa_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: f64 = 0.0;
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2408_ = lean_float_isnan(v_x_2407_);
                if v___x_2408_ == 0 {
                    v___x_2409_ = lean_float_isinf(v_x_2407_);
                    if v___x_2409_ == 0 {
                        v___x_2410_ = crate::leanh::lean_float_once(
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
                                v___x_2414_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
                                return v___x_2414_;
                            } else {
                                v___x_2415_ = lean_float_negate(v_x_2407_);
                                v___x_2416_ = l___private_Lean_Data_Json_Basic_0__Lean_JsonNumber_fromPositiveFloat_x21(v___x_2415_);
                                v_mantissa_2417_ = crate::leanh::lean_ctor_get(v___x_2416_, 0);
                                v_exponent_2418_ = crate::leanh::lean_ctor_get(v___x_2416_, 1);
                                v_isSharedCheck_2427_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2416_)) as u8;
                                if v_isSharedCheck_2427_ == 0 {
                                    v___x_2420_ = v___x_2416_;
                                    v_isShared_2421_ = v_isSharedCheck_2427_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_exponent_2418_);
                                    crate::leanh::lean_inc(v_mantissa_2417_);
                                    crate::leanh::lean_dec(v___x_2416_);
                                    v___x_2420_ = crate::leanh::lean_box(0);
                                    v_isShared_2421_ = v_isSharedCheck_2427_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v___x_2428_ = crate::leanh::lean_obj_once(
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
                        v___x_2429_ = crate::leanh::lean_float_once(
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
                crate::leanh::lean_dec(v_mantissa_2417_);
                if v_isShared_2421_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2420_, 0, v___x_2422_);
                    v___x_2424_ = v___x_2420_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_exponent_2418_);
                    v___x_2424_ = v_reuseFailAlloc_2426_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2424_);
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_JsonNumber_fromFloat_x3f___boxed(
    mut v_x_2434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_2435_: f64 = 0.0;
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_2435_ = crate::leanh::lean_unbox_float(v_x_2434_);
    crate::leanh::lean_dec_ref(v_x_2434_);
    v_res_2436_ = l_Lean_JsonNumber_fromFloat_x3f(v_x_boxed_2435_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_strLt(
    mut v_a_2437_: *mut crate::leanh::LeanObject,
    mut v_b_2438_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2439_: u8 = 0;
    v___x_2439_ = lean_string_dec_lt(v_a_2437_, v_b_2438_);
    return v___x_2439_;
}
pub unsafe fn l_Lean_strLt___boxed(
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_b_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2442_: u8 = 0;
    let mut v_r_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2442_ = l_Lean_strLt(v_a_2440_, v_b_2441_);
    crate::leanh::lean_dec_ref(v_b_2441_);
    crate::leanh::lean_dec_ref(v_a_2440_);
    v_r_2443_ = crate::leanh::lean_box((v_res_2442_) as usize);
    return v_r_2443_;
}
pub unsafe fn l_Lean_Json_ctorIdx(
    mut v_x_2444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_2444_) {
        0 => {
            let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2445_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_2445_;
        }
        1 => {
            let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2446_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_2446_;
        }
        2 => {
            let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2447_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_2447_;
        }
        3 => {
            let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2448_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_2448_;
        }
        4 => {
            let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2449_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_2449_;
        }
        _ => {
            let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2450_ = crate::leanh::lean_unsigned_to_nat(5);
            return v___x_2450_;
        }
    }
}
pub unsafe fn l_Lean_Json_ctorIdx___boxed(
    mut v_x_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_Lean_Json_ctorIdx(v_x_2451_);
    crate::leanh::lean_dec(v_x_2451_);
    return v_res_2452_;
}
pub unsafe fn l_Lean_Json_ctorElim___redArg(
    mut v_t_2453_: *mut crate::leanh::LeanObject,
    mut v_k_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_2453_) {
        0 => {
            return v_k_2454_;
        }
        1 => {
            let mut v_b_2455_: u8 = 0;
            let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_b_2455_ = crate::leanh::lean_ctor_get_uint8(v_t_2453_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_t_2453_, 0);
            v___x_2456_ = crate::leanh::lean_box((v_b_2455_) as usize);
            v___x_2457_ = crate::leanh::lean_apply_1(v_k_2454_, v___x_2456_);
            return v___x_2457_;
        }
        5 => {
            let mut v_kvPairs_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_kvPairs_2458_ = crate::leanh::lean_ctor_get(v_t_2453_, 0);
            crate::leanh::lean_inc(v_kvPairs_2458_);
            crate::leanh::lean_dec_ref_known(v_t_2453_, 1);
            v___x_2459_ = crate::leanh::lean_apply_1(v_k_2454_, v_kvPairs_2458_);
            return v___x_2459_;
        }
        _ => {
            let mut v_n_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_n_2460_ = crate::leanh::lean_ctor_get(v_t_2453_, 0);
            crate::leanh::lean_inc_ref(v_n_2460_);
            crate::leanh::lean_dec(v_t_2453_);
            v___x_2461_ = crate::leanh::lean_apply_1(v_k_2454_, v_n_2460_);
            return v___x_2461_;
        }
    }
}
pub unsafe fn l_Lean_Json_ctorElim(
    mut v_motive__1_2462_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2463_: *mut crate::leanh::LeanObject,
    mut v_t_2464_: *mut crate::leanh::LeanObject,
    mut v_h_2465_: *mut crate::leanh::LeanObject,
    mut v_k_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2467_ = l_Lean_Json_ctorElim___redArg(v_t_2464_, v_k_2466_);
    return v___x_2467_;
}
pub unsafe fn l_Lean_Json_ctorElim___boxed(
    mut v_motive__1_2468_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_2469_: *mut crate::leanh::LeanObject,
    mut v_t_2470_: *mut crate::leanh::LeanObject,
    mut v_h_2471_: *mut crate::leanh::LeanObject,
    mut v_k_2472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2473_ = l_Lean_Json_ctorElim(
        v_motive__1_2468_,
        v_ctorIdx_2469_,
        v_t_2470_,
        v_h_2471_,
        v_k_2472_,
    );
    crate::leanh::lean_dec(v_ctorIdx_2469_);
    return v_res_2473_;
}
pub unsafe fn l_Lean_Json_null_elim___redArg(
    mut v_t_2474_: *mut crate::leanh::LeanObject,
    mut v_null_2475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2476_ = l_Lean_Json_ctorElim___redArg(v_t_2474_, v_null_2475_);
    return v___x_2476_;
}
pub unsafe fn l_Lean_Json_null_elim(
    mut v_motive__1_2477_: *mut crate::leanh::LeanObject,
    mut v_t_2478_: *mut crate::leanh::LeanObject,
    mut v_h_2479_: *mut crate::leanh::LeanObject,
    mut v_null_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = l_Lean_Json_ctorElim___redArg(v_t_2478_, v_null_2480_);
    return v___x_2481_;
}
pub unsafe fn l_Lean_Json_bool_elim___redArg(
    mut v_t_2482_: *mut crate::leanh::LeanObject,
    mut v_bool_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2484_ = l_Lean_Json_ctorElim___redArg(v_t_2482_, v_bool_2483_);
    return v___x_2484_;
}
pub unsafe fn l_Lean_Json_bool_elim(
    mut v_motive__1_2485_: *mut crate::leanh::LeanObject,
    mut v_t_2486_: *mut crate::leanh::LeanObject,
    mut v_h_2487_: *mut crate::leanh::LeanObject,
    mut v_bool_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_Json_ctorElim___redArg(v_t_2486_, v_bool_2488_);
    return v___x_2489_;
}
pub unsafe fn l_Lean_Json_num_elim___redArg(
    mut v_t_2490_: *mut crate::leanh::LeanObject,
    mut v_num_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2492_ = l_Lean_Json_ctorElim___redArg(v_t_2490_, v_num_2491_);
    return v___x_2492_;
}
pub unsafe fn l_Lean_Json_num_elim(
    mut v_motive__1_2493_: *mut crate::leanh::LeanObject,
    mut v_t_2494_: *mut crate::leanh::LeanObject,
    mut v_h_2495_: *mut crate::leanh::LeanObject,
    mut v_num_2496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2497_ = l_Lean_Json_ctorElim___redArg(v_t_2494_, v_num_2496_);
    return v___x_2497_;
}
pub unsafe fn l_Lean_Json_str_elim___redArg(
    mut v_t_2498_: *mut crate::leanh::LeanObject,
    mut v_str_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2500_ = l_Lean_Json_ctorElim___redArg(v_t_2498_, v_str_2499_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_Json_str_elim(
    mut v_motive__1_2501_: *mut crate::leanh::LeanObject,
    mut v_t_2502_: *mut crate::leanh::LeanObject,
    mut v_h_2503_: *mut crate::leanh::LeanObject,
    mut v_str_2504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2505_ = l_Lean_Json_ctorElim___redArg(v_t_2502_, v_str_2504_);
    return v___x_2505_;
}
pub unsafe fn l_Lean_Json_arr_elim___redArg(
    mut v_t_2506_: *mut crate::leanh::LeanObject,
    mut v_arr_2507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l_Lean_Json_ctorElim___redArg(v_t_2506_, v_arr_2507_);
    return v___x_2508_;
}
pub unsafe fn l_Lean_Json_arr_elim(
    mut v_motive__1_2509_: *mut crate::leanh::LeanObject,
    mut v_t_2510_: *mut crate::leanh::LeanObject,
    mut v_h_2511_: *mut crate::leanh::LeanObject,
    mut v_arr_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2513_ = l_Lean_Json_ctorElim___redArg(v_t_2510_, v_arr_2512_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_Json_obj_elim___redArg(
    mut v_t_2514_: *mut crate::leanh::LeanObject,
    mut v_obj_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2516_ = l_Lean_Json_ctorElim___redArg(v_t_2514_, v_obj_2515_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Json_obj_elim(
    mut v_motive__1_2517_: *mut crate::leanh::LeanObject,
    mut v_t_2518_: *mut crate::leanh::LeanObject,
    mut v_h_2519_: *mut crate::leanh::LeanObject,
    mut v_obj_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_Json_ctorElim___redArg(v_t_2518_, v_obj_2520_);
    return v___x_2521_;
}
pub unsafe fn _init_l_Lean_instInhabitedJson_default() -> *mut crate::leanh::LeanObject {
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2522_ = crate::leanh::lean_box(0);
    return v___x_2522_;
}
pub unsafe fn _init_l_Lean_instInhabitedJson() -> *mut crate::leanh::LeanObject {
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2523_ = crate::leanh::lean_box(0);
    return v___x_2523_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(
    mut v_init_2524_: *mut crate::leanh::LeanObject,
    mut v_x_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_l_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2525_) == 0 {
                    v_l_2526_ = crate::leanh::lean_ctor_get(v_x_2525_, 3);
                    v_r_2527_ = crate::leanh::lean_ctor_get(v_x_2525_, 4);
                    v___x_2528_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2524_, v_l_2526_);
                    v___x_2529_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2530_ = lean_nat_add(v___x_2528_, v___x_2529_);
                    crate::leanh::lean_dec(v___x_2528_);
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
    mut v_init_2532_: *mut crate::leanh::LeanObject,
    mut v_x_2533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2534_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2532_, v_x_2533_);
    crate::leanh::lean_dec(v_x_2533_);
    return v_res_2534_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(
    mut v_t_2535_: *mut crate::leanh::LeanObject,
    mut v_k_2536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2535_) == 0 {
                    v_k_2537_ = crate::leanh::lean_ctor_get(v_t_2535_, 1);
                    v_v_2538_ = crate::leanh::lean_ctor_get(v_t_2535_, 2);
                    v_l_2539_ = crate::leanh::lean_ctor_get(v_t_2535_, 3);
                    v_r_2540_ = crate::leanh::lean_ctor_get(v_t_2535_, 4);
                    v___x_2541_ = lean_string_compare(v_k_2536_, v_k_2537_);
                    match v___x_2541_ {
                        0 => {
                            v_t_2535_ = v_l_2539_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2538_);
                            v___x_2543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2543_, 0, v_v_2538_);
                            return v___x_2543_;
                        }
                        _ => {
                            v_t_2535_ = v_r_2540_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2545_ = crate::leanh::lean_box(0);
                    return v___x_2545_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg___boxed(
    mut v_t_2546_: *mut crate::leanh::LeanObject,
    mut v_k_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2548_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_2546_, v_k_2547_);
    crate::leanh::lean_dec_ref(v_k_2547_);
    crate::leanh::lean_dec(v_t_2546_);
    return v_res_2548_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(
    mut v_kvPairs_2552_: *mut crate::leanh::LeanObject,
    mut v_init_2553_: *mut crate::leanh::LeanObject,
    mut v_x_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2562_: u8 = 0;
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2565_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: u8 = 0;
    let mut v_val_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_unused_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2554_) == 0 {
                    v_k_2555_ = crate::leanh::lean_ctor_get(v_x_2554_, 1);
                    v_v_2556_ = crate::leanh::lean_ctor_get(v_x_2554_, 2);
                    v_l_2557_ = crate::leanh::lean_ctor_get(v_x_2554_, 3);
                    v_r_2558_ = crate::leanh::lean_ctor_get(v_x_2554_, 4);
                    v___x_2559_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2552_, v_init_2553_, v_l_2557_);
                    if crate::leanh::lean_obj_tag(v___x_2559_) == 0 {
                        return v___x_2559_;
                    } else {
                        v_isSharedCheck_2578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2559_)) as u8;
                        if v_isSharedCheck_2578_ == 0 {
                            v_unused_2579_ = crate::leanh::lean_ctor_get(v___x_2559_, 0);
                            crate::leanh::lean_dec(v_unused_2579_);
                            v___x_2561_ = v___x_2559_;
                            v_isShared_2562_ = v_isSharedCheck_2578_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2559_);
                            v___x_2561_ = crate::leanh::lean_box(0);
                            v_isShared_2562_ = v_isSharedCheck_2578_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2580_, 0, v_init_2553_);
                    return v___x_2580_;
                }
            }
            1 => {
                v___x_2563_ = crate::leanh::lean_box(0);
                v___x_2572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_2552_, v_k_2555_);
                if crate::leanh::lean_obj_tag(v___x_2572_) == 0 {
                    v___x_2573_ = 0;
                    v___y_2565_ = v___x_2573_;
                    state = 2;
                    continue;
                } else {
                    v_val_2574_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
                    crate::leanh::lean_inc(v_val_2574_);
                    crate::leanh::lean_dec_ref_known(v___x_2572_, 1);
                    v___x_2575_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(
                        v_v_2556_,
                        v_val_2574_,
                    );
                    crate::leanh::lean_dec(v_val_2574_);
                    if v___x_2575_ == 0 {
                        v___y_2565_ = v___x_2575_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_2561_);
                        v___x_2576_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0;
                        v_init_2553_ = v___x_2576_;
                        v_x_2554_ = v_r_2558_;
                        state = 0;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2566_ = crate::leanh::lean_box((v___y_2565_) as usize);
                v___x_2567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2567_, 0, v___x_2566_);
                v___x_2568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                crate::leanh::lean_ctor_set(v___x_2568_, 1, v___x_2563_);
                if v_isShared_2562_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2561_, 0);
                    crate::leanh::lean_ctor_set(v___x_2561_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2561_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
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
    mut v_x_2581_: *mut crate::leanh::LeanObject,
    mut v_x_2582_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2584_: u8 = 0;
    let mut v_b_2585_: u8 = 0;
    let mut v_b_2586_: u8 = 0;
    let mut v___x_2587_: u8 = 0;
    let mut v_b_2588_: u8 = 0;
    let mut v___x_2589_: u8 = 0;
    let mut v_n_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: u8 = 0;
    let mut v___x_2593_: u8 = 0;
    let mut v_s_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: u8 = 0;
    let mut v___x_2597_: u8 = 0;
    let mut v_elems_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_elems_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: u8 = 0;
    let mut v___x_2603_: u8 = 0;
    let mut v___x_2604_: u8 = 0;
    let mut v_kvPairs_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_szA_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_szB_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: u8 = 0;
    let mut v___y_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2581_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 0 {
                        v___x_2583_ = 1;
                        return v___x_2583_;
                    } else {
                        v___x_2584_ = 0;
                        return v___x_2584_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 1 {
                        v_b_2585_ = crate::leanh::lean_ctor_get_uint8(v_x_2581_, 0 as u32);
                        if v_b_2585_ == 0 {
                            v_b_2586_ = crate::leanh::lean_ctor_get_uint8(v_x_2582_, 0 as u32);
                            if v_b_2586_ == 0 {
                                v___x_2587_ = 1;
                                return v___x_2587_;
                            } else {
                                return v_b_2585_;
                            }
                        } else {
                            v_b_2588_ = crate::leanh::lean_ctor_get_uint8(v_x_2582_, 0 as u32);
                            return v_b_2588_;
                        }
                    } else {
                        v___x_2589_ = 0;
                        return v___x_2589_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 2 {
                        v_n_2590_ = crate::leanh::lean_ctor_get(v_x_2581_, 0);
                        v_n_2591_ = crate::leanh::lean_ctor_get(v_x_2582_, 0);
                        v___x_2592_ = l_Lean_instDecidableEqJsonNumber_decEq(v_n_2590_, v_n_2591_);
                        return v___x_2592_;
                    } else {
                        v___x_2593_ = 0;
                        return v___x_2593_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 3 {
                        v_s_2594_ = crate::leanh::lean_ctor_get(v_x_2581_, 0);
                        v_s_2595_ = crate::leanh::lean_ctor_get(v_x_2582_, 0);
                        v___x_2596_ = lean_string_dec_eq(v_s_2594_, v_s_2595_);
                        return v___x_2596_;
                    } else {
                        v___x_2597_ = 0;
                        return v___x_2597_;
                    }
                }
                4 => {
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 4 {
                        v_elems_2598_ = crate::leanh::lean_ctor_get(v_x_2581_, 0);
                        v_elems_2599_ = crate::leanh::lean_ctor_get(v_x_2582_, 0);
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
                    if crate::leanh::lean_obj_tag(v_x_2582_) == 5 {
                        v_kvPairs_2605_ = crate::leanh::lean_ctor_get(v_x_2581_, 0);
                        v_kvPairs_2606_ = crate::leanh::lean_ctor_get(v_x_2582_, 0);
                        v___x_2607_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_szA_2608_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_2607_, v_kvPairs_2605_);
                        v_szB_2609_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v___x_2607_, v_kvPairs_2606_);
                        v___x_2610_ = lean_nat_dec_eq(v_szA_2608_, v_szB_2609_);
                        crate::leanh::lean_dec(v_szB_2609_);
                        crate::leanh::lean_dec(v_szA_2608_);
                        if v___x_2610_ == 0 {
                            return v___x_2610_;
                        } else {
                            v___x_2616_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___closed__0;
                            v___x_2617_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2606_, v___x_2616_, v_kvPairs_2605_);
                            v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2617_, 0);
                            crate::leanh::lean_inc(v_a_2618_);
                            crate::leanh::lean_dec_ref(v___x_2617_);
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
                v_fst_2613_ = crate::leanh::lean_ctor_get(v___y_2612_, 0);
                crate::leanh::lean_inc(v_fst_2613_);
                crate::leanh::lean_dec_ref(v___y_2612_);
                if crate::leanh::lean_obj_tag(v_fst_2613_) == 0 {
                    return v___x_2610_;
                } else {
                    v_val_2614_ = crate::leanh::lean_ctor_get(v_fst_2613_, 0);
                    crate::leanh::lean_inc(v_val_2614_);
                    crate::leanh::lean_dec_ref_known(v_fst_2613_, 1);
                    v___x_2615_ = (crate::leanh::lean_unbox(v_val_2614_) as u8);
                    crate::leanh::lean_dec(v_val_2614_);
                    return v___x_2615_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(
    mut v_xs_2620_: *mut crate::leanh::LeanObject,
    mut v_ys_2621_: *mut crate::leanh::LeanObject,
    mut v_x_2622_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2624_: u8 = 0;
    let mut v_one_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2623_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2624_ = lean_nat_dec_eq(v_x_2622_, v_zero_2623_);
                if v_isZero_2624_ == 1 {
                    crate::leanh::lean_dec(v_x_2622_);
                    return v_isZero_2624_;
                } else {
                    v_one_2625_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_2626_ = lean_nat_sub(v_x_2622_, v_one_2625_);
                    crate::leanh::lean_dec(v_x_2622_);
                    v___x_2627_ = lean_array_fget_borrowed(v_xs_2620_, v_n_2626_);
                    v___x_2628_ = lean_array_fget_borrowed(v_ys_2621_, v_n_2626_);
                    v___x_2629_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(
                        v___x_2627_,
                        v___x_2628_,
                    );
                    if v___x_2629_ == 0 {
                        crate::leanh::lean_dec(v_n_2626_);
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
    mut v_xs_2631_: *mut crate::leanh::LeanObject,
    mut v_ys_2632_: *mut crate::leanh::LeanObject,
    mut v_x_2633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2634_: u8 = 0;
    let mut v_r_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2634_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_2631_, v_ys_2632_, v_x_2633_);
    crate::leanh::lean_dec_ref(v_ys_2632_);
    crate::leanh::lean_dec_ref(v_xs_2631_);
    v_r_2635_ = crate::leanh::lean_box((v_res_2634_) as usize);
    return v_r_2635_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3___boxed(
    mut v_kvPairs_2636_: *mut crate::leanh::LeanObject,
    mut v_init_2637_: *mut crate::leanh::LeanObject,
    mut v_x_2638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2639_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__3(v_kvPairs_2636_, v_init_2637_, v_x_2638_);
    crate::leanh::lean_dec(v_x_2638_);
    crate::leanh::lean_dec(v_kvPairs_2636_);
    return v_res_2639_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27___boxed(
    mut v_x_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2642_: u8 = 0;
    let mut v_r_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2642_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_x_2640_, v_x_2641_);
    crate::leanh::lean_dec(v_x_2641_);
    crate::leanh::lean_dec(v_x_2640_);
    v_r_2643_ = crate::leanh::lean_box((v_res_2642_) as usize);
    return v_r_2643_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(
    mut v_xs_2644_: *mut crate::leanh::LeanObject,
    mut v_ys_2645_: *mut crate::leanh::LeanObject,
    mut v_hsz_2646_: *mut crate::leanh::LeanObject,
    mut v_x_2647_: *mut crate::leanh::LeanObject,
    mut v_x_2648_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2649_: u8 = 0;
    v___x_2649_ = l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___redArg(v_xs_2644_, v_ys_2645_, v_x_2647_);
    return v___x_2649_;
}
pub unsafe fn l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0___boxed(
    mut v_xs_2650_: *mut crate::leanh::LeanObject,
    mut v_ys_2651_: *mut crate::leanh::LeanObject,
    mut v_hsz_2652_: *mut crate::leanh::LeanObject,
    mut v_x_2653_: *mut crate::leanh::LeanObject,
    mut v_x_2654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2655_: u8 = 0;
    let mut v_r_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2655_ =
        l_Array_isEqvAux___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__0(
            v_xs_2650_,
            v_ys_2651_,
            v_hsz_2652_,
            v_x_2653_,
            v_x_2654_,
        );
    crate::leanh::lean_dec_ref(v_ys_2651_);
    crate::leanh::lean_dec_ref(v_xs_2650_);
    v_r_2656_ = crate::leanh::lean_box((v_res_2655_) as usize);
    return v_r_2656_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(
    mut v_init_2657_: *mut crate::leanh::LeanObject,
    mut v_t_2658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1_spec__1(v_init_2657_, v_t_2658_);
    return v___x_2659_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1___boxed(
    mut v_init_2660_: *mut crate::leanh::LeanObject,
    mut v_t_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2662_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__1(v_init_2660_, v_t_2661_);
    crate::leanh::lean_dec(v_t_2661_);
    return v_res_2662_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(
    mut v_00_u03b4_2663_: *mut crate::leanh::LeanObject,
    mut v_t_2664_: *mut crate::leanh::LeanObject,
    mut v_k_2665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2666_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_t_2664_, v_k_2665_);
    return v___x_2666_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___boxed(
    mut v_00_u03b4_2667_: *mut crate::leanh::LeanObject,
    mut v_t_2668_: *mut crate::leanh::LeanObject,
    mut v_k_2669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2670_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2(v_00_u03b4_2667_, v_t_2668_, v_k_2669_);
    crate::leanh::lean_dec_ref(v_k_2669_);
    crate::leanh::lean_dec(v_t_2668_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_Json_instBEq___private__1(
    mut v_a_2671_: *mut crate::leanh::LeanObject,
    mut v_a_2672_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2673_: u8 = 0;
    v___x_2673_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27(v_a_2671_, v_a_2672_);
    return v___x_2673_;
}
pub unsafe fn l_Lean_Json_instBEq___private__1___boxed(
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_a_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2676_: u8 = 0;
    let mut v_r_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2676_ = l_Lean_Json_instBEq___private__1(v_a_2674_, v_a_2675_);
    crate::leanh::lean_dec(v_a_2675_);
    crate::leanh::lean_dec(v_a_2674_);
    v_r_2677_ = crate::leanh::lean_box((v_res_2676_) as usize);
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
    mut v_as_2688_: *mut crate::leanh::LeanObject,
    mut v_i_2689_: usize,
    mut v_stop_2690_: usize,
    mut v_b_2691_: u64,
) -> u64 {
    let mut v___x_2692_: u8 = 0;
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_x_2699_: *mut crate::leanh::LeanObject,
) -> u64 {
    match crate::leanh::lean_obj_tag(v_x_2699_) {
        0 => {
            let mut v___x_2700_: u64 = 0;
            v___x_2700_ = 11u64;
            return v___x_2700_;
        }
        1 => {
            let mut v_b_2701_: u8 = 0;
            v_b_2701_ = crate::leanh::lean_ctor_get_uint8(v_x_2699_, 0 as u32);
            if v_b_2701_ == 0 {
                let mut v___x_2702_: u64 = 0;
                v___x_2702_ = crate::leanh::lean_uint64_once(
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
                v___x_2703_ = crate::leanh::lean_uint64_once(
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
            let mut v_n_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2705_: u64 = 0;
            let mut v___x_2706_: u64 = 0;
            let mut v___x_2707_: u64 = 0;
            v_n_2704_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
            v___x_2705_ = 17u64;
            v___x_2706_ = l_Lean_instHashableJsonNumber_hash(v_n_2704_);
            v___x_2707_ = lean_uint64_mix_hash(v___x_2705_, v___x_2706_);
            return v___x_2707_;
        }
        3 => {
            let mut v_s_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2709_: u64 = 0;
            let mut v___x_2710_: u64 = 0;
            let mut v___x_2711_: u64 = 0;
            v_s_2708_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
            v___x_2709_ = 19u64;
            v___x_2710_ = lean_string_hash(v_s_2708_);
            v___x_2711_ = lean_uint64_mix_hash(v___x_2709_, v___x_2710_);
            return v___x_2711_;
        }
        4 => {
            let mut v_elems_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2713_: u64 = 0;
            let mut v___x_2714_: u64 = 0;
            let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2717_: u8 = 0;
            v_elems_2712_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
            v___x_2713_ = 23u64;
            v___x_2714_ = 7u64;
            v___x_2715_ = crate::leanh::lean_unsigned_to_nat(0);
            v___x_2716_ = lean_array_get_size(v_elems_2712_);
            v___x_2717_ = lean_nat_dec_lt(v___x_2715_, v___x_2716_);
            if v___x_2717_ == 0 {
                let mut v___x_2718_: u64 = 0;
                v___x_2718_ = crate::leanh::lean_uint64_once(
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
                        v___x_2720_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2_once), _init_l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___closed__2);
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
            let mut v_kvPairs_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2730_: u64 = 0;
            let mut v___x_2731_: u64 = 0;
            let mut v___x_2732_: u64 = 0;
            let mut v___x_2733_: u64 = 0;
            v_kvPairs_2729_ = crate::leanh::lean_ctor_get(v_x_2699_, 0);
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
    mut v_x_2735_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v_k_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: u64 = 0;
    let mut v___x_2741_: u64 = 0;
    let mut v___x_2742_: u64 = 0;
    let mut v___x_2743_: u64 = 0;
    let mut v___x_2744_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2735_) == 0 {
                    v_k_2736_ = crate::leanh::lean_ctor_get(v_x_2735_, 1);
                    v_v_2737_ = crate::leanh::lean_ctor_get(v_x_2735_, 2);
                    v_l_2738_ = crate::leanh::lean_ctor_get(v_x_2735_, 3);
                    v_r_2739_ = crate::leanh::lean_ctor_get(v_x_2735_, 4);
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
    mut v_init_2746_: *mut crate::leanh::LeanObject,
    mut v_x_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_boxed_2748_: u64 = 0;
    let mut v_res_2749_: u64 = 0;
    let mut v_r_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_init_boxed_2748_ = crate::leanh::lean_unbox_uint64(v_init_2746_);
    crate::leanh::lean_dec_ref(v_init_2746_);
    v_res_2749_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_boxed_2748_, v_x_2747_);
    crate::leanh::lean_dec(v_x_2747_);
    v_r_2750_ = crate::leanh::lean_box_uint64(v_res_2749_);
    return v_r_2750_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0___boxed(
    mut v_as_2751_: *mut crate::leanh::LeanObject,
    mut v_i_2752_: *mut crate::leanh::LeanObject,
    mut v_stop_2753_: *mut crate::leanh::LeanObject,
    mut v_b_2754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2755_: usize = 0;
    let mut v_stop_boxed_2756_: usize = 0;
    let mut v_b_boxed_2757_: u64 = 0;
    let mut v_res_2758_: u64 = 0;
    let mut v_r_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2755_ = crate::leanh::lean_unbox_usize(v_i_2752_);
    crate::leanh::lean_dec(v_i_2752_);
    v_stop_boxed_2756_ = crate::leanh::lean_unbox_usize(v_stop_2753_);
    crate::leanh::lean_dec(v_stop_2753_);
    v_b_boxed_2757_ = crate::leanh::lean_unbox_uint64(v_b_2754_);
    crate::leanh::lean_dec_ref(v_b_2754_);
    v_res_2758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__0(v_as_2751_, v_i_boxed_2755_, v_stop_boxed_2756_, v_b_boxed_2757_);
    crate::leanh::lean_dec_ref(v_as_2751_);
    v_r_2759_ = crate::leanh::lean_box_uint64(v_res_2758_);
    return v_r_2759_;
}
pub unsafe fn l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27___boxed(
    mut v_x_2760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2761_: u64 = 0;
    let mut v_r_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2761_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_x_2760_);
    crate::leanh::lean_dec(v_x_2760_);
    v_r_2762_ = crate::leanh::lean_box_uint64(v_res_2761_);
    return v_r_2762_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(
    mut v_init_2763_: u64,
    mut v_t_2764_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_2765_: u64 = 0;
    v___x_2765_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1_spec__1(v_init_2763_, v_t_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1___boxed(
    mut v_init_2766_: *mut crate::leanh::LeanObject,
    mut v_t_2767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_boxed_2768_: u64 = 0;
    let mut v_res_2769_: u64 = 0;
    let mut v_r_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_init_boxed_2768_ = crate::leanh::lean_unbox_uint64(v_init_2766_);
    crate::leanh::lean_dec_ref(v_init_2766_);
    v_res_2769_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27_spec__1(v_init_boxed_2768_, v_t_2767_);
    crate::leanh::lean_dec(v_t_2767_);
    v_r_2770_ = crate::leanh::lean_box_uint64(v_res_2769_);
    return v_r_2770_;
}
pub unsafe fn l_Lean_Json_instHashable___private__1(
    mut v_a_2771_: *mut crate::leanh::LeanObject,
) -> u64 {
    let mut v___x_2772_: u64 = 0;
    v___x_2772_ = l___private_Lean_Data_Json_Basic_0__Lean_Json_hash_x27(v_a_2771_);
    return v___x_2772_;
}
pub unsafe fn l_Lean_Json_instHashable___private__1___boxed(
    mut v_a_2773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2774_: u64 = 0;
    let mut v_r_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2774_ = l_Lean_Json_instHashable___private__1(v_a_2773_);
    crate::leanh::lean_dec(v_a_2773_);
    v_r_2775_ = crate::leanh::lean_box_uint64(v_res_2774_);
    return v_r_2775_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(
    mut v_k_2778_: *mut crate::leanh::LeanObject,
    mut v_v_2779_: *mut crate::leanh::LeanObject,
    mut v_t_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: u8 = 0;
    let mut v_impl_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: u8 = 0;
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2808_: u8 = 0;
    let mut v_size_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u8 = 0;
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2846_: u8 = 0;
    let mut v_unused_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2864_: u8 = 0;
    let mut v_unused_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_unused_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2883_: u8 = 0;
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2891_: u8 = 0;
    let mut v_unused_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v_k_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2915_: u8 = 0;
    let mut v_unused_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut v_unused_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2948_: u8 = 0;
    let mut v_size_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2960_: u8 = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_unused_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2998_: u8 = 0;
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3002_: u8 = 0;
    let mut v_unused_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3009_: u8 = 0;
    let mut v_unused_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3021_: u8 = 0;
    let mut v_k_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_unused_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3041_: u8 = 0;
    let mut v_unused_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3057_: u8 = 0;
    let mut v_unused_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3065_: u8 = 0;
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2780_) == 0 {
                    v_size_2781_ = crate::leanh::lean_ctor_get(v_t_2780_, 0);
                    v_k_2782_ = crate::leanh::lean_ctor_get(v_t_2780_, 1);
                    v_v_2783_ = crate::leanh::lean_ctor_get(v_t_2780_, 2);
                    v_l_2784_ = crate::leanh::lean_ctor_get(v_t_2780_, 3);
                    v_r_2785_ = crate::leanh::lean_ctor_get(v_t_2780_, 4);
                    v_isSharedCheck_3065_ = (!crate::leanh::lean_is_exclusive(v_t_2780_)) as u8;
                    if v_isSharedCheck_3065_ == 0 {
                        v___x_2787_ = v_t_2780_;
                        v_isShared_2788_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_2785_);
                        crate::leanh::lean_inc(v_l_2784_);
                        crate::leanh::lean_inc(v_v_2783_);
                        crate::leanh::lean_inc(v_k_2782_);
                        crate::leanh::lean_inc(v_size_2781_);
                        crate::leanh::lean_dec(v_t_2780_);
                        v___x_2787_ = crate::leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_3065_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3066_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3067_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3067_, 0, v___x_3066_);
                    crate::leanh::lean_ctor_set(v___x_3067_, 1, v_k_2778_);
                    crate::leanh::lean_ctor_set(v___x_3067_, 2, v_v_2779_);
                    crate::leanh::lean_ctor_set(v___x_3067_, 3, v_t_2780_);
                    crate::leanh::lean_ctor_set(v___x_3067_, 4, v_t_2780_);
                    return v___x_3067_;
                }
            }
            1 => {
                v___x_2789_ = lean_string_compare(v_k_2778_, v_k_2782_);
                match v___x_2789_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_2781_);
                        v_impl_2790_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_2778_, v_v_2779_, v_l_2784_);
                        v___x_2791_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_r_2785_) == 0 {
                            v_size_2792_ = crate::leanh::lean_ctor_get(v_r_2785_, 0);
                            v_size_2793_ = crate::leanh::lean_ctor_get(v_impl_2790_, 0);
                            crate::leanh::lean_inc(v_size_2793_);
                            v_k_2794_ = crate::leanh::lean_ctor_get(v_impl_2790_, 1);
                            crate::leanh::lean_inc(v_k_2794_);
                            v_v_2795_ = crate::leanh::lean_ctor_get(v_impl_2790_, 2);
                            crate::leanh::lean_inc(v_v_2795_);
                            v_l_2796_ = crate::leanh::lean_ctor_get(v_impl_2790_, 3);
                            crate::leanh::lean_inc(v_l_2796_);
                            v_r_2797_ = crate::leanh::lean_ctor_get(v_impl_2790_, 4);
                            crate::leanh::lean_inc(v_r_2797_);
                            v___x_2798_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2799_ = lean_nat_mul(v___x_2798_, v_size_2792_);
                            v___x_2800_ = lean_nat_dec_lt(v___x_2799_, v_size_2793_);
                            crate::leanh::lean_dec(v___x_2799_);
                            if v___x_2800_ == 0 {
                                crate::leanh::lean_dec(v_r_2797_);
                                crate::leanh::lean_dec(v_l_2796_);
                                crate::leanh::lean_dec(v_v_2795_);
                                crate::leanh::lean_dec(v_k_2794_);
                                v___x_2801_ = lean_nat_add(v___x_2791_, v_size_2793_);
                                crate::leanh::lean_dec(v_size_2793_);
                                v___x_2802_ = lean_nat_add(v___x_2801_, v_size_2792_);
                                crate::leanh::lean_dec(v___x_2801_);
                                if v_isShared_2788_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v_impl_2790_);
                                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2802_);
                                    v___x_2804_ = v___x_2787_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2805_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2805_,
                                        0,
                                        v___x_2802_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2805_,
                                        1,
                                        v_k_2782_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2805_,
                                        2,
                                        v_v_2783_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2805_,
                                        3,
                                        v_impl_2790_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2805_,
                                        4,
                                        v_r_2785_,
                                    );
                                    v___x_2804_ = v_reuseFailAlloc_2805_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_2871_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2790_)) as u8;
                                if v_isSharedCheck_2871_ == 0 {
                                    v_unused_2872_ = crate::leanh::lean_ctor_get(v_impl_2790_, 4);
                                    crate::leanh::lean_dec(v_unused_2872_);
                                    v_unused_2873_ = crate::leanh::lean_ctor_get(v_impl_2790_, 3);
                                    crate::leanh::lean_dec(v_unused_2873_);
                                    v_unused_2874_ = crate::leanh::lean_ctor_get(v_impl_2790_, 2);
                                    crate::leanh::lean_dec(v_unused_2874_);
                                    v_unused_2875_ = crate::leanh::lean_ctor_get(v_impl_2790_, 1);
                                    crate::leanh::lean_dec(v_unused_2875_);
                                    v_unused_2876_ = crate::leanh::lean_ctor_get(v_impl_2790_, 0);
                                    crate::leanh::lean_dec(v_unused_2876_);
                                    v___x_2807_ = v_impl_2790_;
                                    v_isShared_2808_ = v_isSharedCheck_2871_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2790_);
                                    v___x_2807_ = crate::leanh::lean_box(0);
                                    v_isShared_2808_ = v_isSharedCheck_2871_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_2877_ = crate::leanh::lean_ctor_get(v_impl_2790_, 3);
                            crate::leanh::lean_inc(v_l_2877_);
                            if crate::leanh::lean_obj_tag(v_l_2877_) == 0 {
                                v_r_2878_ = crate::leanh::lean_ctor_get(v_impl_2790_, 4);
                                v_k_2879_ = crate::leanh::lean_ctor_get(v_impl_2790_, 1);
                                v_v_2880_ = crate::leanh::lean_ctor_get(v_impl_2790_, 2);
                                v_isSharedCheck_2891_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2790_)) as u8;
                                if v_isSharedCheck_2891_ == 0 {
                                    v_unused_2892_ = crate::leanh::lean_ctor_get(v_impl_2790_, 3);
                                    crate::leanh::lean_dec(v_unused_2892_);
                                    v_unused_2893_ = crate::leanh::lean_ctor_get(v_impl_2790_, 0);
                                    crate::leanh::lean_dec(v_unused_2893_);
                                    v___x_2882_ = v_impl_2790_;
                                    v_isShared_2883_ = v_isSharedCheck_2891_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_2878_);
                                    crate::leanh::lean_inc(v_v_2880_);
                                    crate::leanh::lean_inc(v_k_2879_);
                                    crate::leanh::lean_dec(v_impl_2790_);
                                    v___x_2882_ = crate::leanh::lean_box(0);
                                    v_isShared_2883_ = v_isSharedCheck_2891_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_2894_ = crate::leanh::lean_ctor_get(v_impl_2790_, 4);
                                crate::leanh::lean_inc(v_r_2894_);
                                if crate::leanh::lean_obj_tag(v_r_2894_) == 0 {
                                    v_k_2895_ = crate::leanh::lean_ctor_get(v_impl_2790_, 1);
                                    v_v_2896_ = crate::leanh::lean_ctor_get(v_impl_2790_, 2);
                                    v_isSharedCheck_2919_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2790_)) as u8;
                                    if v_isSharedCheck_2919_ == 0 {
                                        v_unused_2920_ =
                                            crate::leanh::lean_ctor_get(v_impl_2790_, 4);
                                        crate::leanh::lean_dec(v_unused_2920_);
                                        v_unused_2921_ =
                                            crate::leanh::lean_ctor_get(v_impl_2790_, 3);
                                        crate::leanh::lean_dec(v_unused_2921_);
                                        v_unused_2922_ =
                                            crate::leanh::lean_ctor_get(v_impl_2790_, 0);
                                        crate::leanh::lean_dec(v_unused_2922_);
                                        v___x_2898_ = v_impl_2790_;
                                        v_isShared_2899_ = v_isSharedCheck_2919_;
                                        state = 16;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_2896_);
                                        crate::leanh::lean_inc(v_k_2895_);
                                        crate::leanh::lean_dec(v_impl_2790_);
                                        v___x_2898_ = crate::leanh::lean_box(0);
                                        v_isShared_2899_ = v_isSharedCheck_2919_;
                                        state = 16;
                                        continue;
                                    }
                                } else {
                                    v___x_2923_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2788_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2787_, 4, v_r_2894_);
                                        crate::leanh::lean_ctor_set(v___x_2787_, 3, v_impl_2790_);
                                        crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2923_);
                                        v___x_2925_ = v___x_2787_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2926_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2926_,
                                            0,
                                            v___x_2923_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2926_,
                                            1,
                                            v_k_2782_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2926_,
                                            2,
                                            v_v_2783_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2926_,
                                            3,
                                            v_impl_2790_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2926_,
                                            4,
                                            v_r_2894_,
                                        );
                                        v___x_2925_ = v_reuseFailAlloc_2926_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_2783_);
                        crate::leanh::lean_dec(v_k_2782_);
                        if v_isShared_2788_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2779_);
                            crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2778_);
                            v___x_2928_ = v___x_2787_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_2929_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_size_2781_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_k_2778_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_v_2779_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_l_2784_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 4, v_r_2785_);
                            v___x_2928_ = v_reuseFailAlloc_2929_;
                            state = 22;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_2781_);
                        v_impl_2930_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(v_k_2778_, v_v_2779_, v_r_2785_);
                        v___x_2931_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_2784_) == 0 {
                            v_size_2932_ = crate::leanh::lean_ctor_get(v_l_2784_, 0);
                            v_size_2933_ = crate::leanh::lean_ctor_get(v_impl_2930_, 0);
                            crate::leanh::lean_inc(v_size_2933_);
                            v_k_2934_ = crate::leanh::lean_ctor_get(v_impl_2930_, 1);
                            crate::leanh::lean_inc(v_k_2934_);
                            v_v_2935_ = crate::leanh::lean_ctor_get(v_impl_2930_, 2);
                            crate::leanh::lean_inc(v_v_2935_);
                            v_l_2936_ = crate::leanh::lean_ctor_get(v_impl_2930_, 3);
                            crate::leanh::lean_inc(v_l_2936_);
                            v_r_2937_ = crate::leanh::lean_ctor_get(v_impl_2930_, 4);
                            crate::leanh::lean_inc(v_r_2937_);
                            v___x_2938_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_2939_ = lean_nat_mul(v___x_2938_, v_size_2932_);
                            v___x_2940_ = lean_nat_dec_lt(v___x_2939_, v_size_2933_);
                            crate::leanh::lean_dec(v___x_2939_);
                            if v___x_2940_ == 0 {
                                crate::leanh::lean_dec(v_r_2937_);
                                crate::leanh::lean_dec(v_l_2936_);
                                crate::leanh::lean_dec(v_v_2935_);
                                crate::leanh::lean_dec(v_k_2934_);
                                v___x_2941_ = lean_nat_add(v___x_2931_, v_size_2932_);
                                v___x_2942_ = lean_nat_add(v___x_2941_, v_size_2933_);
                                crate::leanh::lean_dec(v_size_2933_);
                                crate::leanh::lean_dec(v___x_2941_);
                                if v_isShared_2788_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v_impl_2930_);
                                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2942_);
                                    v___x_2944_ = v___x_2787_;
                                    state = 23;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2945_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2945_,
                                        0,
                                        v___x_2942_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2945_,
                                        1,
                                        v_k_2782_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2945_,
                                        2,
                                        v_v_2783_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2945_,
                                        3,
                                        v_l_2784_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2945_,
                                        4,
                                        v_impl_2930_,
                                    );
                                    v___x_2944_ = v_reuseFailAlloc_2945_;
                                    state = 23;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_3009_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2930_)) as u8;
                                if v_isSharedCheck_3009_ == 0 {
                                    v_unused_3010_ = crate::leanh::lean_ctor_get(v_impl_2930_, 4);
                                    crate::leanh::lean_dec(v_unused_3010_);
                                    v_unused_3011_ = crate::leanh::lean_ctor_get(v_impl_2930_, 3);
                                    crate::leanh::lean_dec(v_unused_3011_);
                                    v_unused_3012_ = crate::leanh::lean_ctor_get(v_impl_2930_, 2);
                                    crate::leanh::lean_dec(v_unused_3012_);
                                    v_unused_3013_ = crate::leanh::lean_ctor_get(v_impl_2930_, 1);
                                    crate::leanh::lean_dec(v_unused_3013_);
                                    v_unused_3014_ = crate::leanh::lean_ctor_get(v_impl_2930_, 0);
                                    crate::leanh::lean_dec(v_unused_3014_);
                                    v___x_2947_ = v_impl_2930_;
                                    v_isShared_2948_ = v_isSharedCheck_3009_;
                                    state = 24;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_2930_);
                                    v___x_2947_ = crate::leanh::lean_box(0);
                                    v_isShared_2948_ = v_isSharedCheck_3009_;
                                    state = 24;
                                    continue;
                                }
                            }
                        } else {
                            v_l_3015_ = crate::leanh::lean_ctor_get(v_impl_2930_, 3);
                            crate::leanh::lean_inc(v_l_3015_);
                            if crate::leanh::lean_obj_tag(v_l_3015_) == 0 {
                                v_r_3016_ = crate::leanh::lean_ctor_get(v_impl_2930_, 4);
                                v_k_3017_ = crate::leanh::lean_ctor_get(v_impl_2930_, 1);
                                v_v_3018_ = crate::leanh::lean_ctor_get(v_impl_2930_, 2);
                                v_isSharedCheck_3041_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_2930_)) as u8;
                                if v_isSharedCheck_3041_ == 0 {
                                    v_unused_3042_ = crate::leanh::lean_ctor_get(v_impl_2930_, 3);
                                    crate::leanh::lean_dec(v_unused_3042_);
                                    v_unused_3043_ = crate::leanh::lean_ctor_get(v_impl_2930_, 0);
                                    crate::leanh::lean_dec(v_unused_3043_);
                                    v___x_3020_ = v_impl_2930_;
                                    v_isShared_3021_ = v_isSharedCheck_3041_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_3016_);
                                    crate::leanh::lean_inc(v_v_3018_);
                                    crate::leanh::lean_inc(v_k_3017_);
                                    crate::leanh::lean_dec(v_impl_2930_);
                                    v___x_3020_ = crate::leanh::lean_box(0);
                                    v_isShared_3021_ = v_isSharedCheck_3041_;
                                    state = 34;
                                    continue;
                                }
                            } else {
                                v_r_3044_ = crate::leanh::lean_ctor_get(v_impl_2930_, 4);
                                crate::leanh::lean_inc(v_r_3044_);
                                if crate::leanh::lean_obj_tag(v_r_3044_) == 0 {
                                    v_k_3045_ = crate::leanh::lean_ctor_get(v_impl_2930_, 1);
                                    v_v_3046_ = crate::leanh::lean_ctor_get(v_impl_2930_, 2);
                                    v_isSharedCheck_3057_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_2930_)) as u8;
                                    if v_isSharedCheck_3057_ == 0 {
                                        v_unused_3058_ =
                                            crate::leanh::lean_ctor_get(v_impl_2930_, 4);
                                        crate::leanh::lean_dec(v_unused_3058_);
                                        v_unused_3059_ =
                                            crate::leanh::lean_ctor_get(v_impl_2930_, 3);
                                        crate::leanh::lean_dec(v_unused_3059_);
                                        v_unused_3060_ =
                                            crate::leanh::lean_ctor_get(v_impl_2930_, 0);
                                        crate::leanh::lean_dec(v_unused_3060_);
                                        v___x_3048_ = v_impl_2930_;
                                        v_isShared_3049_ = v_isSharedCheck_3057_;
                                        state = 39;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_3046_);
                                        crate::leanh::lean_inc(v_k_3045_);
                                        crate::leanh::lean_dec(v_impl_2930_);
                                        v___x_3048_ = crate::leanh::lean_box(0);
                                        v_isShared_3049_ = v_isSharedCheck_3057_;
                                        state = 39;
                                        continue;
                                    }
                                } else {
                                    v___x_3061_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_2788_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_2787_, 4, v_impl_2930_);
                                        crate::leanh::lean_ctor_set(v___x_2787_, 3, v_r_3044_);
                                        crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_3061_);
                                        v___x_3063_ = v___x_2787_;
                                        state = 42;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3064_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3064_,
                                            0,
                                            v___x_3061_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3064_,
                                            1,
                                            v_k_2782_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3064_,
                                            2,
                                            v_v_2783_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3064_,
                                            3,
                                            v_r_3044_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3064_,
                                            4,
                                            v_impl_2930_,
                                        );
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
                v_size_2809_ = crate::leanh::lean_ctor_get(v_l_2796_, 0);
                v_size_2810_ = crate::leanh::lean_ctor_get(v_r_2797_, 0);
                v_k_2811_ = crate::leanh::lean_ctor_get(v_r_2797_, 1);
                v_v_2812_ = crate::leanh::lean_ctor_get(v_r_2797_, 2);
                v_l_2813_ = crate::leanh::lean_ctor_get(v_r_2797_, 3);
                v_r_2814_ = crate::leanh::lean_ctor_get(v_r_2797_, 4);
                v___x_2815_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2816_ = lean_nat_mul(v___x_2815_, v_size_2809_);
                v___x_2817_ = lean_nat_dec_lt(v_size_2810_, v___x_2816_);
                crate::leanh::lean_dec(v___x_2816_);
                if v___x_2817_ == 0 {
                    crate::leanh::lean_inc(v_r_2814_);
                    crate::leanh::lean_inc(v_l_2813_);
                    crate::leanh::lean_inc(v_v_2812_);
                    crate::leanh::lean_inc(v_k_2811_);
                    v_isSharedCheck_2846_ = (!crate::leanh::lean_is_exclusive(v_r_2797_)) as u8;
                    if v_isSharedCheck_2846_ == 0 {
                        v_unused_2847_ = crate::leanh::lean_ctor_get(v_r_2797_, 4);
                        crate::leanh::lean_dec(v_unused_2847_);
                        v_unused_2848_ = crate::leanh::lean_ctor_get(v_r_2797_, 3);
                        crate::leanh::lean_dec(v_unused_2848_);
                        v_unused_2849_ = crate::leanh::lean_ctor_get(v_r_2797_, 2);
                        crate::leanh::lean_dec(v_unused_2849_);
                        v_unused_2850_ = crate::leanh::lean_ctor_get(v_r_2797_, 1);
                        crate::leanh::lean_dec(v_unused_2850_);
                        v_unused_2851_ = crate::leanh::lean_ctor_get(v_r_2797_, 0);
                        crate::leanh::lean_dec(v_unused_2851_);
                        v___x_2819_ = v_r_2797_;
                        v_isShared_2820_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_2797_);
                        v___x_2819_ = crate::leanh::lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2846_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2787_);
                    v___x_2852_ = lean_nat_add(v___x_2791_, v_size_2793_);
                    crate::leanh::lean_dec(v_size_2793_);
                    v___x_2853_ = lean_nat_add(v___x_2852_, v_size_2792_);
                    crate::leanh::lean_dec(v___x_2852_);
                    v___x_2854_ = lean_nat_add(v___x_2791_, v_size_2792_);
                    v___x_2855_ = lean_nat_add(v___x_2854_, v_size_2810_);
                    crate::leanh::lean_dec(v___x_2854_);
                    crate::leanh::lean_inc_ref(v_r_2785_);
                    if v_isShared_2808_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2807_, 4, v_r_2785_);
                        crate::leanh::lean_ctor_set(v___x_2807_, 3, v_r_2797_);
                        crate::leanh::lean_ctor_set(v___x_2807_, 2, v_v_2783_);
                        crate::leanh::lean_ctor_set(v___x_2807_, 1, v_k_2782_);
                        crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2855_);
                        v___x_2857_ = v___x_2807_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2870_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2855_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_k_2782_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 2, v_v_2783_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 3, v_r_2797_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2870_, 4, v_r_2785_);
                        v___x_2857_ = v_reuseFailAlloc_2870_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_2821_ = lean_nat_add(v___x_2791_, v_size_2793_);
                crate::leanh::lean_dec(v_size_2793_);
                v___x_2822_ = lean_nat_add(v___x_2821_, v_size_2792_);
                crate::leanh::lean_dec(v___x_2821_);
                v___x_2834_ = lean_nat_add(v___x_2791_, v_size_2809_);
                if crate::leanh::lean_obj_tag(v_l_2813_) == 0 {
                    v_size_2844_ = crate::leanh::lean_ctor_get(v_l_2813_, 0);
                    crate::leanh::lean_inc(v_size_2844_);
                    v___y_2836_ = v_size_2844_;
                    state = 8;
                    continue;
                } else {
                    v___x_2845_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2836_ = v___x_2845_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_2827_ = lean_nat_add(v___y_2825_, v___y_2826_);
                crate::leanh::lean_dec(v___y_2826_);
                crate::leanh::lean_dec(v___y_2825_);
                if v_isShared_2820_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2819_, 4, v_r_2785_);
                    crate::leanh::lean_ctor_set(v___x_2819_, 3, v_r_2814_);
                    crate::leanh::lean_ctor_set(v___x_2819_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v___x_2819_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v___x_2819_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2833_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 0, v___x_2827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 3, v_r_2814_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2833_, 4, v_r_2785_);
                    v___x_2829_ = v_reuseFailAlloc_2833_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2807_, 4, v___x_2829_);
                    crate::leanh::lean_ctor_set(v___x_2807_, 3, v___y_2824_);
                    crate::leanh::lean_ctor_set(v___x_2807_, 2, v_v_2812_);
                    crate::leanh::lean_ctor_set(v___x_2807_, 1, v_k_2811_);
                    crate::leanh::lean_ctor_set(v___x_2807_, 0, v___x_2822_);
                    v___x_2831_ = v___x_2807_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 1, v_k_2811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 2, v_v_2812_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 3, v___y_2824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2832_, 4, v___x_2829_);
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
                crate::leanh::lean_dec(v___y_2836_);
                crate::leanh::lean_dec(v___x_2834_);
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v_l_2813_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v_l_2796_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2795_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2794_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2837_);
                    v___x_2839_ = v___x_2787_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 1, v_k_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 2, v_v_2795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 3, v_l_2796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2843_, 4, v_l_2813_);
                    v___x_2839_ = v_reuseFailAlloc_2843_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2840_ = lean_nat_add(v___x_2791_, v_size_2792_);
                if crate::leanh::lean_obj_tag(v_r_2814_) == 0 {
                    v_size_2841_ = crate::leanh::lean_ctor_get(v_r_2814_, 0);
                    crate::leanh::lean_inc(v_size_2841_);
                    v___y_2824_ = v___x_2839_;
                    v___y_2825_ = v___x_2840_;
                    v___y_2826_ = v_size_2841_;
                    state = 5;
                    continue;
                } else {
                    v___x_2842_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2824_ = v___x_2839_;
                    v___y_2825_ = v___x_2840_;
                    v___y_2826_ = v___x_2842_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_2864_ = (!crate::leanh::lean_is_exclusive(v_r_2785_)) as u8;
                if v_isSharedCheck_2864_ == 0 {
                    v_unused_2865_ = crate::leanh::lean_ctor_get(v_r_2785_, 4);
                    crate::leanh::lean_dec(v_unused_2865_);
                    v_unused_2866_ = crate::leanh::lean_ctor_get(v_r_2785_, 3);
                    crate::leanh::lean_dec(v_unused_2866_);
                    v_unused_2867_ = crate::leanh::lean_ctor_get(v_r_2785_, 2);
                    crate::leanh::lean_dec(v_unused_2867_);
                    v_unused_2868_ = crate::leanh::lean_ctor_get(v_r_2785_, 1);
                    crate::leanh::lean_dec(v_unused_2868_);
                    v_unused_2869_ = crate::leanh::lean_ctor_get(v_r_2785_, 0);
                    crate::leanh::lean_dec(v_unused_2869_);
                    v___x_2859_ = v_r_2785_;
                    v_isShared_2860_ = v_isSharedCheck_2864_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_2785_);
                    v___x_2859_ = crate::leanh::lean_box(0);
                    v_isShared_2860_ = v_isSharedCheck_2864_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_2860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2859_, 4, v___x_2857_);
                    crate::leanh::lean_ctor_set(v___x_2859_, 3, v_l_2796_);
                    crate::leanh::lean_ctor_set(v___x_2859_, 2, v_v_2795_);
                    crate::leanh::lean_ctor_set(v___x_2859_, 1, v_k_2794_);
                    crate::leanh::lean_ctor_set(v___x_2859_, 0, v___x_2853_);
                    v___x_2862_ = v___x_2859_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2863_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 1, v_k_2794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 2, v_v_2795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 3, v_l_2796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2863_, 4, v___x_2857_);
                    v___x_2862_ = v_reuseFailAlloc_2863_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2862_;
            }
            13 => {
                v___x_2884_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_2878_);
                if v_isShared_2883_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2882_, 3, v_r_2878_);
                    crate::leanh::lean_ctor_set(v___x_2882_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v___x_2882_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v___x_2882_, 0, v___x_2791_);
                    v___x_2886_ = v___x_2882_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2890_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 3, v_r_2878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2890_, 4, v_r_2878_);
                    v___x_2886_ = v_reuseFailAlloc_2890_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v___x_2886_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v_l_2877_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2880_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2879_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2884_);
                    v___x_2888_ = v___x_2787_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2889_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 0, v___x_2884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 1, v_k_2879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 2, v_v_2880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 3, v_l_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2889_, 4, v___x_2886_);
                    v___x_2888_ = v_reuseFailAlloc_2889_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2888_;
            }
            16 => {
                v_k_2900_ = crate::leanh::lean_ctor_get(v_r_2894_, 1);
                v_v_2901_ = crate::leanh::lean_ctor_get(v_r_2894_, 2);
                v_isSharedCheck_2915_ = (!crate::leanh::lean_is_exclusive(v_r_2894_)) as u8;
                if v_isSharedCheck_2915_ == 0 {
                    v_unused_2916_ = crate::leanh::lean_ctor_get(v_r_2894_, 4);
                    crate::leanh::lean_dec(v_unused_2916_);
                    v_unused_2917_ = crate::leanh::lean_ctor_get(v_r_2894_, 3);
                    crate::leanh::lean_dec(v_unused_2917_);
                    v_unused_2918_ = crate::leanh::lean_ctor_get(v_r_2894_, 0);
                    crate::leanh::lean_dec(v_unused_2918_);
                    v___x_2903_ = v_r_2894_;
                    v_isShared_2904_ = v_isSharedCheck_2915_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2901_);
                    crate::leanh::lean_inc(v_k_2900_);
                    crate::leanh::lean_dec(v_r_2894_);
                    v___x_2903_ = crate::leanh::lean_box(0);
                    v_isShared_2904_ = v_isSharedCheck_2915_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_2905_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_2904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2903_, 4, v_l_2877_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 3, v_l_2877_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 2, v_v_2896_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 1, v_k_2895_);
                    crate::leanh::lean_ctor_set(v___x_2903_, 0, v___x_2791_);
                    v___x_2907_ = v___x_2903_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2914_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 1, v_k_2895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 2, v_v_2896_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 3, v_l_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2914_, 4, v_l_2877_);
                    v___x_2907_ = v_reuseFailAlloc_2914_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_2899_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2898_, 4, v_l_2877_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v___x_2898_, 0, v___x_2791_);
                    v___x_2909_ = v___x_2898_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2913_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 0, v___x_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_l_2877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2913_, 4, v_l_2877_);
                    v___x_2909_ = v_reuseFailAlloc_2913_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v___x_2909_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v___x_2907_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_2901_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_2900_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2905_);
                    v___x_2911_ = v___x_2787_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2912_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2905_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_k_2900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_v_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 3, v___x_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2912_, 4, v___x_2909_);
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
                v_size_2949_ = crate::leanh::lean_ctor_get(v_l_2936_, 0);
                v_k_2950_ = crate::leanh::lean_ctor_get(v_l_2936_, 1);
                v_v_2951_ = crate::leanh::lean_ctor_get(v_l_2936_, 2);
                v_l_2952_ = crate::leanh::lean_ctor_get(v_l_2936_, 3);
                v_r_2953_ = crate::leanh::lean_ctor_get(v_l_2936_, 4);
                v_size_2954_ = crate::leanh::lean_ctor_get(v_r_2937_, 0);
                v___x_2955_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2956_ = lean_nat_mul(v___x_2955_, v_size_2954_);
                v___x_2957_ = lean_nat_dec_lt(v_size_2949_, v___x_2956_);
                crate::leanh::lean_dec(v___x_2956_);
                if v___x_2957_ == 0 {
                    crate::leanh::lean_inc(v_r_2953_);
                    crate::leanh::lean_inc(v_l_2952_);
                    crate::leanh::lean_inc(v_v_2951_);
                    crate::leanh::lean_inc(v_k_2950_);
                    v_isSharedCheck_2985_ = (!crate::leanh::lean_is_exclusive(v_l_2936_)) as u8;
                    if v_isSharedCheck_2985_ == 0 {
                        v_unused_2986_ = crate::leanh::lean_ctor_get(v_l_2936_, 4);
                        crate::leanh::lean_dec(v_unused_2986_);
                        v_unused_2987_ = crate::leanh::lean_ctor_get(v_l_2936_, 3);
                        crate::leanh::lean_dec(v_unused_2987_);
                        v_unused_2988_ = crate::leanh::lean_ctor_get(v_l_2936_, 2);
                        crate::leanh::lean_dec(v_unused_2988_);
                        v_unused_2989_ = crate::leanh::lean_ctor_get(v_l_2936_, 1);
                        crate::leanh::lean_dec(v_unused_2989_);
                        v_unused_2990_ = crate::leanh::lean_ctor_get(v_l_2936_, 0);
                        crate::leanh::lean_dec(v_unused_2990_);
                        v___x_2959_ = v_l_2936_;
                        v_isShared_2960_ = v_isSharedCheck_2985_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_2936_);
                        v___x_2959_ = crate::leanh::lean_box(0);
                        v_isShared_2960_ = v_isSharedCheck_2985_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2787_);
                    v___x_2991_ = lean_nat_add(v___x_2931_, v_size_2932_);
                    v___x_2992_ = lean_nat_add(v___x_2991_, v_size_2933_);
                    crate::leanh::lean_dec(v_size_2933_);
                    v___x_2993_ = lean_nat_add(v___x_2991_, v_size_2949_);
                    crate::leanh::lean_dec(v___x_2991_);
                    crate::leanh::lean_inc_ref(v_l_2784_);
                    if v_isShared_2948_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2947_, 4, v_l_2936_);
                        crate::leanh::lean_ctor_set(v___x_2947_, 3, v_l_2784_);
                        crate::leanh::lean_ctor_set(v___x_2947_, 2, v_v_2783_);
                        crate::leanh::lean_ctor_set(v___x_2947_, 1, v_k_2782_);
                        crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2993_);
                        v___x_2995_ = v___x_2947_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3008_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 0, v___x_2993_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_k_2782_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_v_2783_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_l_2784_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3008_, 4, v_l_2936_);
                        v___x_2995_ = v_reuseFailAlloc_3008_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_2961_ = lean_nat_add(v___x_2931_, v_size_2932_);
                v___x_2962_ = lean_nat_add(v___x_2961_, v_size_2933_);
                crate::leanh::lean_dec(v_size_2933_);
                if crate::leanh::lean_obj_tag(v_l_2952_) == 0 {
                    v_size_2983_ = crate::leanh::lean_ctor_get(v_l_2952_, 0);
                    crate::leanh::lean_inc(v_size_2983_);
                    v___y_2975_ = v_size_2983_;
                    state = 29;
                    continue;
                } else {
                    v___x_2984_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2975_ = v___x_2984_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_2967_ = lean_nat_add(v___y_2965_, v___y_2966_);
                crate::leanh::lean_dec(v___y_2966_);
                crate::leanh::lean_dec(v___y_2965_);
                if v_isShared_2960_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2959_, 4, v_r_2937_);
                    crate::leanh::lean_ctor_set(v___x_2959_, 3, v_r_2953_);
                    crate::leanh::lean_ctor_set(v___x_2959_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v___x_2959_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v___x_2959_, 0, v___x_2967_);
                    v___x_2969_ = v___x_2959_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2967_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_r_2953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 4, v_r_2937_);
                    v___x_2969_ = v_reuseFailAlloc_2973_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2948_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2947_, 4, v___x_2969_);
                    crate::leanh::lean_ctor_set(v___x_2947_, 3, v___y_2964_);
                    crate::leanh::lean_ctor_set(v___x_2947_, 2, v_v_2951_);
                    crate::leanh::lean_ctor_set(v___x_2947_, 1, v_k_2950_);
                    crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2962_);
                    v___x_2971_ = v___x_2947_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2972_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 0, v___x_2962_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_k_2950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 2, v_v_2951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 3, v___y_2964_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2972_, 4, v___x_2969_);
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
                crate::leanh::lean_dec(v___y_2975_);
                crate::leanh::lean_dec(v___x_2961_);
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v_l_2952_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2976_);
                    v___x_2978_ = v___x_2787_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 3, v_l_2784_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 4, v_l_2952_);
                    v___x_2978_ = v_reuseFailAlloc_2982_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_2979_ = lean_nat_add(v___x_2931_, v_size_2954_);
                if crate::leanh::lean_obj_tag(v_r_2953_) == 0 {
                    v_size_2980_ = crate::leanh::lean_ctor_get(v_r_2953_, 0);
                    crate::leanh::lean_inc(v_size_2980_);
                    v___y_2964_ = v___x_2978_;
                    v___y_2965_ = v___x_2979_;
                    v___y_2966_ = v_size_2980_;
                    state = 26;
                    continue;
                } else {
                    v___x_2981_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2964_ = v___x_2978_;
                    v___y_2965_ = v___x_2979_;
                    v___y_2966_ = v___x_2981_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_3002_ = (!crate::leanh::lean_is_exclusive(v_l_2784_)) as u8;
                if v_isSharedCheck_3002_ == 0 {
                    v_unused_3003_ = crate::leanh::lean_ctor_get(v_l_2784_, 4);
                    crate::leanh::lean_dec(v_unused_3003_);
                    v_unused_3004_ = crate::leanh::lean_ctor_get(v_l_2784_, 3);
                    crate::leanh::lean_dec(v_unused_3004_);
                    v_unused_3005_ = crate::leanh::lean_ctor_get(v_l_2784_, 2);
                    crate::leanh::lean_dec(v_unused_3005_);
                    v_unused_3006_ = crate::leanh::lean_ctor_get(v_l_2784_, 1);
                    crate::leanh::lean_dec(v_unused_3006_);
                    v_unused_3007_ = crate::leanh::lean_ctor_get(v_l_2784_, 0);
                    crate::leanh::lean_dec(v_unused_3007_);
                    v___x_2997_ = v_l_2784_;
                    v_isShared_2998_ = v_isSharedCheck_3002_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_2784_);
                    v___x_2997_ = crate::leanh::lean_box(0);
                    v_isShared_2998_ = v_isSharedCheck_3002_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2997_, 4, v_r_2937_);
                    crate::leanh::lean_ctor_set(v___x_2997_, 3, v___x_2995_);
                    crate::leanh::lean_ctor_set(v___x_2997_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v___x_2997_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v___x_2997_, 0, v___x_2992_);
                    v___x_3000_ = v___x_2997_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3001_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 1, v_k_2934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 2, v_v_2935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 3, v___x_2995_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3001_, 4, v_r_2937_);
                    v___x_3000_ = v_reuseFailAlloc_3001_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3000_;
            }
            34 => {
                v_k_3022_ = crate::leanh::lean_ctor_get(v_l_3015_, 1);
                v_v_3023_ = crate::leanh::lean_ctor_get(v_l_3015_, 2);
                v_isSharedCheck_3037_ = (!crate::leanh::lean_is_exclusive(v_l_3015_)) as u8;
                if v_isSharedCheck_3037_ == 0 {
                    v_unused_3038_ = crate::leanh::lean_ctor_get(v_l_3015_, 4);
                    crate::leanh::lean_dec(v_unused_3038_);
                    v_unused_3039_ = crate::leanh::lean_ctor_get(v_l_3015_, 3);
                    crate::leanh::lean_dec(v_unused_3039_);
                    v_unused_3040_ = crate::leanh::lean_ctor_get(v_l_3015_, 0);
                    crate::leanh::lean_dec(v_unused_3040_);
                    v___x_3025_ = v_l_3015_;
                    v_isShared_3026_ = v_isSharedCheck_3037_;
                    state = 35;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3023_);
                    crate::leanh::lean_inc(v_k_3022_);
                    crate::leanh::lean_dec(v_l_3015_);
                    v___x_3025_ = crate::leanh::lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3037_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3027_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_3016_, 2);
                if v_isShared_3026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3025_, 4, v_r_3016_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 3, v_r_3016_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_2931_);
                    v___x_3029_ = v___x_3025_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_2931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 3, v_r_3016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 4, v_r_3016_);
                    v___x_3029_ = v_reuseFailAlloc_3036_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                crate::leanh::lean_inc(v_r_3016_);
                if v_isShared_3021_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3020_, 3, v_r_3016_);
                    crate::leanh::lean_ctor_set(v___x_3020_, 0, v___x_2931_);
                    v___x_3031_ = v___x_3020_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_2931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 1, v_k_3017_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 2, v_v_3018_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 3, v_r_3016_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3035_, 4, v_r_3016_);
                    v___x_3031_ = v_reuseFailAlloc_3035_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v___x_3031_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v___x_3029_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_3023_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_3022_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_3027_);
                    v___x_3033_ = v___x_2787_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_k_3022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 2, v_v_3023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 3, v___x_3029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 4, v___x_3031_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3033_;
            }
            39 => {
                v___x_3050_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3048_, 4, v_l_3015_);
                    crate::leanh::lean_ctor_set(v___x_3048_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v___x_3048_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v___x_3048_, 0, v___x_2931_);
                    v___x_3052_ = v___x_3048_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3056_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_2931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 1, v_k_2782_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 2, v_v_2783_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 3, v_l_3015_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3056_, 4, v_l_3015_);
                    v___x_3052_ = v_reuseFailAlloc_3056_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 4, v_r_3044_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 3, v___x_3052_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 2, v_v_3046_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_k_3045_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_3050_);
                    v___x_3054_ = v___x_2787_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 0, v___x_3050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 1, v_k_3045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 2, v_v_3046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 3, v___x_3052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3055_, 4, v_r_3044_);
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
    mut v_as_x27_3068_: *mut crate::leanh::LeanObject,
    mut v_b_3069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3068_) == 0 {
                    return v_b_3069_;
                } else {
                    v_head_3070_ = crate::leanh::lean_ctor_get(v_as_x27_3068_, 0);
                    v_tail_3071_ = crate::leanh::lean_ctor_get(v_as_x27_3068_, 1);
                    v_fst_3072_ = crate::leanh::lean_ctor_get(v_head_3070_, 0);
                    v_snd_3073_ = crate::leanh::lean_ctor_get(v_head_3070_, 1);
                    crate::leanh::lean_inc(v_snd_3073_);
                    crate::leanh::lean_inc(v_fst_3072_);
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
    mut v_as_x27_3076_: *mut crate::leanh::LeanObject,
    mut v_b_3077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3078_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_3076_, v_b_3077_);
    crate::leanh::lean_dec(v_as_x27_3076_);
    return v_res_3078_;
}
pub unsafe fn l_Lean_Json_mkObj(
    mut v_o_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_r_3080_ = crate::leanh::lean_box(1);
    v___x_3081_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_o_3079_, v_r_3080_);
    v___x_3082_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3082_, 0, v___x_3081_);
    return v___x_3082_;
}
pub unsafe fn l_Lean_Json_mkObj___boxed(
    mut v_o_3083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3084_ = l_Lean_Json_mkObj(v_o_3083_);
    crate::leanh::lean_dec(v_o_3083_);
    return v_res_3084_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0(
    mut v_00_u03b2_3085_: *mut crate::leanh::LeanObject,
    mut v_k_3086_: *mut crate::leanh::LeanObject,
    mut v_v_3087_: *mut crate::leanh::LeanObject,
    mut v_t_3088_: *mut crate::leanh::LeanObject,
    mut v_hl_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3090_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Json_mkObj_spec__0___redArg(
        v_k_3086_, v_v_3087_, v_t_3088_,
    );
    return v___x_3090_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(
    mut v_as_3091_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3092_: *mut crate::leanh::LeanObject,
    mut v_b_3093_: *mut crate::leanh::LeanObject,
    mut v_a_3094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3095_ =
        l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___redArg(v_as_x27_3092_, v_b_3093_);
    return v___x_3095_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1___boxed(
    mut v_as_3096_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3097_: *mut crate::leanh::LeanObject,
    mut v_b_3098_: *mut crate::leanh::LeanObject,
    mut v_a_3099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l_List_forIn_x27_loop___at___00Lean_Json_mkObj_spec__1(
        v_as_3096_,
        v_as_x27_3097_,
        v_b_3098_,
        v_a_3099_,
    );
    crate::leanh::lean_dec(v_as_x27_3097_);
    crate::leanh::lean_dec(v_as_3096_);
    return v_res_3100_;
}
pub unsafe fn l_Lean_Json_instCoeNat___lam__0(
    mut v_n_3101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3102_ = l_Lean_JsonNumber_fromNat(v_n_3101_);
    v___x_3103_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3103_, 0, v___x_3102_);
    return v___x_3103_;
}
pub unsafe fn l_Lean_Json_instCoeInt___lam__0(
    mut v_n_3106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3107_ = l_Lean_JsonNumber_fromInt(v_n_3106_);
    v___x_3108_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3108_, 0, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_Json_instCoeString___lam__0(
    mut v_s_3111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3112_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3112_, 0, v_s_3111_);
    return v___x_3112_;
}
pub unsafe fn l_Lean_Json_instCoeBool___lam__0(mut v_b_3115_: u8) -> *mut crate::leanh::LeanObject {
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3116_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
    crate::leanh::lean_ctor_set_uint8(v___x_3116_, 0 as u32, v_b_3115_);
    return v___x_3116_;
}
pub unsafe fn l_Lean_Json_instCoeBool___lam__0___boxed(
    mut v_b_3117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_boxed_3118_: u8 = 0;
    let mut v_res_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_3118_ = (crate::leanh::lean_unbox(v_b_3117_) as u8);
    v_res_3119_ = l_Lean_Json_instCoeBool___lam__0(v_b_boxed_3118_);
    return v_res_3119_;
}
pub unsafe fn l_Lean_Json_instOfNat(
    mut v_n_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3123_ = l_Lean_JsonNumber_fromNat(v_n_3122_);
    v___x_3124_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3124_, 0, v___x_3123_);
    return v___x_3124_;
}
pub unsafe fn l_Lean_Json_isNull(mut v_x_3125_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3125_) == 0 {
        let mut v___x_3126_: u8 = 0;
        v___x_3126_ = 1;
        return v___x_3126_;
    } else {
        let mut v___x_3127_: u8 = 0;
        v___x_3127_ = 0;
        return v___x_3127_;
    }
}
pub unsafe fn l_Lean_Json_isNull___boxed(
    mut v_x_3128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3129_: u8 = 0;
    let mut v_r_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3129_ = l_Lean_Json_isNull(v_x_3128_);
    crate::leanh::lean_dec(v_x_3128_);
    v_r_3130_ = crate::leanh::lean_box((v_res_3129_) as usize);
    return v_r_3130_;
}
pub unsafe fn l_Lean_Json_getObj_x3f(
    mut v_x_3134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kvPairs_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3138_: u8 = 0;
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3142_: u8 = 0;
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3134_) == 5 {
                    v_kvPairs_3135_ = crate::leanh::lean_ctor_get(v_x_3134_, 0);
                    v_isSharedCheck_3142_ = (!crate::leanh::lean_is_exclusive(v_x_3134_)) as u8;
                    if v_isSharedCheck_3142_ == 0 {
                        v___x_3137_ = v_x_3134_;
                        v_isShared_3138_ = v_isSharedCheck_3142_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_kvPairs_3135_);
                        crate::leanh::lean_dec(v_x_3134_);
                        v___x_3137_ = crate::leanh::lean_box(0);
                        v_isShared_3138_ = v_isSharedCheck_3142_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3134_);
                    v___x_3143_ = l_Lean_Json_getObj_x3f___closed__1;
                    return v___x_3143_;
                }
            }
            1 => {
                if v_isShared_3138_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3137_, 1);
                    v___x_3140_ = v___x_3137_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_kvPairs_3135_);
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
pub unsafe fn l_Lean_Json_getArr_x3f(
    mut v_x_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elems_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3147_) == 4 {
                    v_elems_3148_ = crate::leanh::lean_ctor_get(v_x_3147_, 0);
                    v_isSharedCheck_3155_ = (!crate::leanh::lean_is_exclusive(v_x_3147_)) as u8;
                    if v_isSharedCheck_3155_ == 0 {
                        v___x_3150_ = v_x_3147_;
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_elems_3148_);
                        crate::leanh::lean_dec(v_x_3147_);
                        v___x_3150_ = crate::leanh::lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3147_);
                    v___x_3156_ = l_Lean_Json_getArr_x3f___closed__1;
                    return v___x_3156_;
                }
            }
            1 => {
                if v_isShared_3151_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3150_, 1);
                    v___x_3153_ = v___x_3150_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_elems_3148_);
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
pub unsafe fn l_Lean_Json_getStr_x3f(
    mut v_x_3160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3160_) == 3 {
                    v_s_3161_ = crate::leanh::lean_ctor_get(v_x_3160_, 0);
                    v_isSharedCheck_3168_ = (!crate::leanh::lean_is_exclusive(v_x_3160_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3163_ = v_x_3160_;
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_s_3161_);
                        crate::leanh::lean_dec(v_x_3160_);
                        v___x_3163_ = crate::leanh::lean_box(0);
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3160_);
                    v___x_3169_ = l_Lean_Json_getStr_x3f___closed__1;
                    return v___x_3169_;
                }
            }
            1 => {
                if v_isShared_3164_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3163_, 1);
                    v___x_3166_ = v___x_3163_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_s_3161_);
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
pub unsafe fn l_Lean_Json_getNat_x3f(
    mut v_x_3173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3179_: u8 = 0;
    let mut v_mantissa_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_3184_: u8 = 0;
    let mut v___x_3185_: u8 = 0;
    let mut v_a_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3173_) == 2 {
                    v_n_3176_ = crate::leanh::lean_ctor_get(v_x_3173_, 0);
                    v_isSharedCheck_3190_ = (!crate::leanh::lean_is_exclusive(v_x_3173_)) as u8;
                    if v_isSharedCheck_3190_ == 0 {
                        v___x_3178_ = v_x_3173_;
                        v_isShared_3179_ = v_isSharedCheck_3190_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_3176_);
                        crate::leanh::lean_dec(v_x_3173_);
                        v___x_3178_ = crate::leanh::lean_box(0);
                        v_isShared_3179_ = v_isSharedCheck_3190_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3173_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3175_ = l_Lean_Json_getNat_x3f___closed__1;
                return v___x_3175_;
            }
            2 => {
                v_mantissa_3180_ = crate::leanh::lean_ctor_get(v_n_3176_, 0);
                crate::leanh::lean_inc(v_mantissa_3180_);
                v_exponent_3181_ = crate::leanh::lean_ctor_get(v_n_3176_, 1);
                crate::leanh::lean_inc(v_exponent_3181_);
                crate::leanh::lean_dec_ref(v_n_3176_);
                v_natZero_3182_ = crate::leanh::lean_unsigned_to_nat(0);
                v_intZero_3183_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_instHashableJsonNumber_hash___closed__0_once),
                    _init_l_Lean_instHashableJsonNumber_hash___closed__0,
                );
                v_isNeg_3184_ = lean_int_dec_lt(v_mantissa_3180_, v_intZero_3183_);
                if v_isNeg_3184_ == 0 {
                    v___x_3185_ = lean_nat_dec_eq(v_exponent_3181_, v_natZero_3182_);
                    crate::leanh::lean_dec(v_exponent_3181_);
                    if v___x_3185_ == 0 {
                        crate::leanh::lean_dec(v_mantissa_3180_);
                        crate::leanh::lean_del_object(v___x_3178_);
                        state = 1;
                        continue;
                    } else {
                        v_a_3186_ = lean_nat_abs(v_mantissa_3180_);
                        crate::leanh::lean_dec(v_mantissa_3180_);
                        if v_isShared_3179_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_3178_, 1);
                            crate::leanh::lean_ctor_set(v___x_3178_, 0, v_a_3186_);
                            v___x_3188_ = v___x_3178_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3189_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_a_3186_);
                            v___x_3188_ = v_reuseFailAlloc_3189_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_exponent_3181_);
                    crate::leanh::lean_dec(v_mantissa_3180_);
                    crate::leanh::lean_del_object(v___x_3178_);
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
pub unsafe fn l_Lean_Json_getInt_x3f(
    mut v_x_3194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3200_: u8 = 0;
    let mut v_mantissa_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exponent_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: u8 = 0;
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3208_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3194_) == 2 {
                    v_n_3197_ = crate::leanh::lean_ctor_get(v_x_3194_, 0);
                    v_isSharedCheck_3208_ = (!crate::leanh::lean_is_exclusive(v_x_3194_)) as u8;
                    if v_isSharedCheck_3208_ == 0 {
                        v___x_3199_ = v_x_3194_;
                        v_isShared_3200_ = v_isSharedCheck_3208_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_3197_);
                        crate::leanh::lean_dec(v_x_3194_);
                        v___x_3199_ = crate::leanh::lean_box(0);
                        v_isShared_3200_ = v_isSharedCheck_3208_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3194_);
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3196_ = l_Lean_Json_getInt_x3f___closed__1;
                return v___x_3196_;
            }
            2 => {
                v_mantissa_3201_ = crate::leanh::lean_ctor_get(v_n_3197_, 0);
                crate::leanh::lean_inc(v_mantissa_3201_);
                v_exponent_3202_ = crate::leanh::lean_ctor_get(v_n_3197_, 1);
                crate::leanh::lean_inc(v_exponent_3202_);
                crate::leanh::lean_dec_ref(v_n_3197_);
                v___x_3203_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3204_ = lean_nat_dec_eq(v_exponent_3202_, v___x_3203_);
                crate::leanh::lean_dec(v_exponent_3202_);
                if v___x_3204_ == 0 {
                    crate::leanh::lean_dec(v_mantissa_3201_);
                    crate::leanh::lean_del_object(v___x_3199_);
                    state = 1;
                    continue;
                } else {
                    if v_isShared_3200_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3199_, 1);
                        crate::leanh::lean_ctor_set(v___x_3199_, 0, v_mantissa_3201_);
                        v___x_3206_ = v___x_3199_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_mantissa_3201_);
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
pub unsafe fn l_Lean_Json_getBool_x3f(
    mut v_x_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3212_) == 1 {
        let mut v_b_3213_: u8 = 0;
        let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_b_3213_ = crate::leanh::lean_ctor_get_uint8(v_x_3212_, 0 as u32);
        v___x_3214_ = crate::leanh::lean_box((v_b_3213_) as usize);
        v___x_3215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3215_, 0, v___x_3214_);
        return v___x_3215_;
    } else {
        let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3216_ = l_Lean_Json_getBool_x3f___closed__1;
        return v___x_3216_;
    }
}
pub unsafe fn l_Lean_Json_getBool_x3f___boxed(
    mut v_x_3217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3218_ = l_Lean_Json_getBool_x3f(v_x_3217_);
    crate::leanh::lean_dec(v_x_3217_);
    return v_res_3218_;
}
pub unsafe fn l_Lean_Json_getNum_x3f(
    mut v_x_3222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3226_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3230_: u8 = 0;
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3222_) == 2 {
                    v_n_3223_ = crate::leanh::lean_ctor_get(v_x_3222_, 0);
                    v_isSharedCheck_3230_ = (!crate::leanh::lean_is_exclusive(v_x_3222_)) as u8;
                    if v_isSharedCheck_3230_ == 0 {
                        v___x_3225_ = v_x_3222_;
                        v_isShared_3226_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_n_3223_);
                        crate::leanh::lean_dec(v_x_3222_);
                        v___x_3225_ = crate::leanh::lean_box(0);
                        v_isShared_3226_ = v_isSharedCheck_3230_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3222_);
                    v___x_3231_ = l_Lean_Json_getNum_x3f___closed__1;
                    return v___x_3231_;
                }
            }
            1 => {
                if v_isShared_3226_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3225_, 1);
                    v___x_3228_ = v___x_3225_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3229_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3229_, 0, v_n_3223_);
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
    mut v_x_3235_: *mut crate::leanh::LeanObject,
    mut v_x_3236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kvPairs_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3250_: u8 = 0;
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3254_: u8 = 0;
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3235_) == 5 {
                    v_kvPairs_3237_ = crate::leanh::lean_ctor_get(v_x_3235_, 0);
                    v_isSharedCheck_3255_ = (!crate::leanh::lean_is_exclusive(v_x_3235_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3239_ = v_x_3235_;
                        v_isShared_3240_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_kvPairs_3237_);
                        crate::leanh::lean_dec(v_x_3235_);
                        v___x_3239_ = crate::leanh::lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3255_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3235_);
                    v___x_3256_ = l_Lean_Json_getObjVal_x3f___closed__1;
                    return v___x_3256_;
                }
            }
            1 => {
                v___x_3241_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Data_Json_Basic_0__Lean_Json_beq_x27_spec__2___redArg(v_kvPairs_3237_, v_x_3236_);
                crate::leanh::lean_dec(v_kvPairs_3237_);
                if crate::leanh::lean_obj_tag(v___x_3241_) == 0 {
                    v___x_3242_ = l_Lean_Json_getObjVal_x3f___closed__0;
                    v___x_3243_ = lean_string_append(v___x_3242_, v_x_3236_);
                    if v_isShared_3240_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3239_, 0);
                        crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3243_);
                        v___x_3245_ = v___x_3239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
                        v___x_3245_ = v_reuseFailAlloc_3246_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3239_);
                    v_val_3247_ = crate::leanh::lean_ctor_get(v___x_3241_, 0);
                    v_isSharedCheck_3254_ = (!crate::leanh::lean_is_exclusive(v___x_3241_)) as u8;
                    if v_isSharedCheck_3254_ == 0 {
                        v___x_3249_ = v___x_3241_;
                        v_isShared_3250_ = v_isSharedCheck_3254_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3247_);
                        crate::leanh::lean_dec(v___x_3241_);
                        v___x_3249_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_3253_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_val_3247_);
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
    mut v_x_3257_: *mut crate::leanh::LeanObject,
    mut v_x_3258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3259_ = l_Lean_Json_getObjVal_x3f(v_x_3257_, v_x_3258_);
    crate::leanh::lean_dec_ref(v_x_3258_);
    return v_res_3259_;
}
pub unsafe fn l_Lean_Json_getArrVal_x3f(
    mut v_x_3263_: *mut crate::leanh::LeanObject,
    mut v_x_3264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_elems_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: u8 = 0;
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3281_: u8 = 0;
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3263_) == 4 {
                    v_elems_3265_ = crate::leanh::lean_ctor_get(v_x_3263_, 0);
                    v_isSharedCheck_3281_ = (!crate::leanh::lean_is_exclusive(v_x_3263_)) as u8;
                    if v_isSharedCheck_3281_ == 0 {
                        v___x_3267_ = v_x_3263_;
                        v_isShared_3268_ = v_isSharedCheck_3281_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_elems_3265_);
                        crate::leanh::lean_dec(v_x_3263_);
                        v___x_3267_ = crate::leanh::lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3281_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3264_);
                    crate::leanh::lean_dec(v_x_3263_);
                    v___x_3282_ = l_Lean_Json_getArrVal_x3f___closed__1;
                    return v___x_3282_;
                }
            }
            1 => {
                v___x_3269_ = lean_array_get_size(v_elems_3265_);
                v___x_3270_ = lean_nat_dec_lt(v_x_3264_, v___x_3269_);
                if v___x_3270_ == 0 {
                    crate::leanh::lean_dec_ref(v_elems_3265_);
                    v___x_3271_ = l_Lean_Json_getArrVal_x3f___closed__0;
                    v___x_3272_ = l_Nat_reprFast(v_x_3264_);
                    v___x_3273_ = lean_string_append(v___x_3271_, v___x_3272_);
                    crate::leanh::lean_dec_ref(v___x_3272_);
                    if v_isShared_3268_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3267_, 0);
                        crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3273_);
                        v___x_3275_ = v___x_3267_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3276_, 0, v___x_3273_);
                        v___x_3275_ = v_reuseFailAlloc_3276_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3277_ = lean_array_fget(v_elems_3265_, v_x_3264_);
                    crate::leanh::lean_dec(v_x_3264_);
                    crate::leanh::lean_dec_ref(v_elems_3265_);
                    if v_isShared_3268_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_3267_, 1);
                        crate::leanh::lean_ctor_set(v___x_3267_, 0, v___x_3277_);
                        v___x_3279_ = v___x_3267_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3277_);
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
    mut v_j_3283_: *mut crate::leanh::LeanObject,
    mut v_k_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3285_ = l_Lean_Json_getObjVal_x3f(v_j_3283_, v_k_3284_);
    if crate::leanh::lean_obj_tag(v___x_3285_) == 0 {
        let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_3285_, 1);
        v___x_3286_ = crate::leanh::lean_box(0);
        return v___x_3286_;
    } else {
        let mut v_a_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_3287_ = crate::leanh::lean_ctor_get(v___x_3285_, 0);
        crate::leanh::lean_inc(v_a_3287_);
        crate::leanh::lean_dec_ref_known(v___x_3285_, 1);
        return v_a_3287_;
    }
}
pub unsafe fn l_Lean_Json_getObjValD___boxed(
    mut v_j_3288_: *mut crate::leanh::LeanObject,
    mut v_k_3289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3290_ = l_Lean_Json_getObjValD(v_j_3288_, v_k_3289_);
    crate::leanh::lean_dec_ref(v_k_3289_);
    return v_res_3290_;
}
pub unsafe fn l_panic___at___00Lean_Json_setObjVal_x21_spec__1(
    mut v_msg_3291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3292_ = crate::leanh::lean_box(0);
    v___x_3293_ = lean_panic_fn_borrowed(v___x_3292_, v_msg_3291_);
    return v___x_3293_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(
    mut v_msg_3294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3295_ = crate::leanh::lean_box(1);
    v___x_3296_ = lean_panic_fn_borrowed(v___x_3295_, v_msg_3294_);
    return v___x_3296_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3300_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2;
    v___x_3301_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_3302_ = crate::leanh::lean_unsigned_to_nat(182);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3306_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__2;
    v___x_3307_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_3308_ = crate::leanh::lean_unsigned_to_nat(183);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3314_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6;
    v___x_3315_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_3316_ = crate::leanh::lean_unsigned_to_nat(276);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3320_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__6;
    v___x_3321_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_3322_ = crate::leanh::lean_unsigned_to_nat(277);
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
    mut v_k_3326_: *mut crate::leanh::LeanObject,
    mut v_v_3327_: *mut crate::leanh::LeanObject,
    mut v_t_3328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3356_: u8 = 0;
    let mut v_size_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3368_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3395_: u8 = 0;
    let mut v_unused_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3410_: u8 = 0;
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3414_: u8 = 0;
    let mut v_unused_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3425_: u8 = 0;
    let mut v_unused_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v_size_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3455_: u8 = 0;
    let mut v_unused_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3462_: u8 = 0;
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3471_: u8 = 0;
    let mut v_unused_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3480_: u8 = 0;
    let mut v_k_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3485_: u8 = 0;
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3497_: u8 = 0;
    let mut v_unused_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut v_unused_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: u8 = 0;
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3534_: u8 = 0;
    let mut v_size_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_unused_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3586_: u8 = 0;
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3590_: u8 = 0;
    let mut v_unused_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3601_: u8 = 0;
    let mut v_unused_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3620_: u8 = 0;
    let mut v_size_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3638_: u8 = 0;
    let mut v_k_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_unused_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3659_: u8 = 0;
    let mut v_unused_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3668_: u8 = 0;
    let mut v___x_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3677_: u8 = 0;
    let mut v_unused_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3328_) == 0 {
                    v_size_3329_ = crate::leanh::lean_ctor_get(v_t_3328_, 0);
                    v_k_3330_ = crate::leanh::lean_ctor_get(v_t_3328_, 1);
                    v_v_3331_ = crate::leanh::lean_ctor_get(v_t_3328_, 2);
                    v_l_3332_ = crate::leanh::lean_ctor_get(v_t_3328_, 3);
                    v_r_3333_ = crate::leanh::lean_ctor_get(v_t_3328_, 4);
                    v_isSharedCheck_3689_ = (!crate::leanh::lean_is_exclusive(v_t_3328_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v___x_3335_ = v_t_3328_;
                        v_isShared_3336_ = v_isSharedCheck_3689_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3333_);
                        crate::leanh::lean_inc(v_l_3332_);
                        crate::leanh::lean_inc(v_v_3331_);
                        crate::leanh::lean_inc(v_k_3330_);
                        crate::leanh::lean_inc(v_size_3329_);
                        crate::leanh::lean_dec(v_t_3328_);
                        v___x_3335_ = crate::leanh::lean_box(0);
                        v_isShared_3336_ = v_isSharedCheck_3689_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3691_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3691_, 0, v___x_3690_);
                    crate::leanh::lean_ctor_set(v___x_3691_, 1, v_k_3326_);
                    crate::leanh::lean_ctor_set(v___x_3691_, 2, v_v_3327_);
                    crate::leanh::lean_ctor_set(v___x_3691_, 3, v_t_3328_);
                    crate::leanh::lean_ctor_set(v___x_3691_, 4, v_t_3328_);
                    return v___x_3691_;
                }
            }
            1 => {
                v___x_3337_ = lean_string_compare(v_k_3326_, v_k_3330_);
                match v___x_3337_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_3329_);
                        v___x_3338_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_3326_, v_v_3327_, v_l_3332_);
                        if crate::leanh::lean_obj_tag(v_r_3333_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_3338_) == 0 {
                                v_size_3339_ = crate::leanh::lean_ctor_get(v_r_3333_, 0);
                                v_size_3340_ = crate::leanh::lean_ctor_get(v___x_3338_, 0);
                                crate::leanh::lean_inc(v_size_3340_);
                                v_k_3341_ = crate::leanh::lean_ctor_get(v___x_3338_, 1);
                                crate::leanh::lean_inc(v_k_3341_);
                                v_v_3342_ = crate::leanh::lean_ctor_get(v___x_3338_, 2);
                                crate::leanh::lean_inc(v_v_3342_);
                                v_l_3343_ = crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                crate::leanh::lean_inc(v_l_3343_);
                                v_r_3344_ = crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                crate::leanh::lean_inc(v_r_3344_);
                                v___x_3345_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3346_ = lean_nat_mul(v___x_3345_, v_size_3339_);
                                v___x_3347_ = lean_nat_dec_lt(v___x_3346_, v_size_3340_);
                                crate::leanh::lean_dec(v___x_3346_);
                                if v___x_3347_ == 0 {
                                    crate::leanh::lean_dec(v_r_3344_);
                                    crate::leanh::lean_dec(v_l_3343_);
                                    crate::leanh::lean_dec(v_v_3342_);
                                    crate::leanh::lean_dec(v_k_3341_);
                                    v___x_3348_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_3349_ = lean_nat_add(v___x_3348_, v_size_3340_);
                                    crate::leanh::lean_dec(v_size_3340_);
                                    v___x_3350_ = lean_nat_add(v___x_3349_, v_size_3339_);
                                    crate::leanh::lean_dec(v___x_3349_);
                                    if v_isShared_3336_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                        crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3350_);
                                        v___x_3352_ = v___x_3335_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3353_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3353_,
                                            0,
                                            v___x_3350_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3353_,
                                            1,
                                            v_k_3330_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3353_,
                                            2,
                                            v_v_3331_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3353_,
                                            3,
                                            v___x_3338_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3353_,
                                            4,
                                            v_r_3333_,
                                        );
                                        v___x_3352_ = v_reuseFailAlloc_3353_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3425_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3338_)) as u8;
                                    if v_isSharedCheck_3425_ == 0 {
                                        v_unused_3426_ =
                                            crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                        crate::leanh::lean_dec(v_unused_3426_);
                                        v_unused_3427_ =
                                            crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                        crate::leanh::lean_dec(v_unused_3427_);
                                        v_unused_3428_ =
                                            crate::leanh::lean_ctor_get(v___x_3338_, 2);
                                        crate::leanh::lean_dec(v_unused_3428_);
                                        v_unused_3429_ =
                                            crate::leanh::lean_ctor_get(v___x_3338_, 1);
                                        crate::leanh::lean_dec(v_unused_3429_);
                                        v_unused_3430_ =
                                            crate::leanh::lean_ctor_get(v___x_3338_, 0);
                                        crate::leanh::lean_dec(v_unused_3430_);
                                        v___x_3355_ = v___x_3338_;
                                        v_isShared_3356_ = v_isSharedCheck_3425_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3338_);
                                        v___x_3355_ = crate::leanh::lean_box(0);
                                        v_isShared_3356_ = v_isSharedCheck_3425_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3431_ = crate::leanh::lean_ctor_get(v_r_3333_, 0);
                                v___x_3432_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3433_ = lean_nat_add(v___x_3432_, v_size_3431_);
                                if v_isShared_3336_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3433_);
                                    v___x_3435_ = v___x_3335_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3436_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3436_,
                                        0,
                                        v___x_3433_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3436_,
                                        1,
                                        v_k_3330_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3436_,
                                        2,
                                        v_v_3331_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3436_,
                                        3,
                                        v___x_3338_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3436_,
                                        4,
                                        v_r_3333_,
                                    );
                                    v___x_3435_ = v_reuseFailAlloc_3436_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3338_) == 0 {
                                v_l_3437_ = crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                crate::leanh::lean_inc(v_l_3437_);
                                if crate::leanh::lean_obj_tag(v_l_3437_) == 0 {
                                    v_r_3438_ = crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                    crate::leanh::lean_inc(v_r_3438_);
                                    if crate::leanh::lean_obj_tag(v_r_3438_) == 0 {
                                        v_size_3439_ = crate::leanh::lean_ctor_get(v___x_3338_, 0);
                                        v_k_3440_ = crate::leanh::lean_ctor_get(v___x_3338_, 1);
                                        v_v_3441_ = crate::leanh::lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3455_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3455_ == 0 {
                                            v_unused_3456_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                            crate::leanh::lean_dec(v_unused_3456_);
                                            v_unused_3457_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                            crate::leanh::lean_dec(v_unused_3457_);
                                            v___x_3443_ = v___x_3338_;
                                            v_isShared_3444_ = v_isSharedCheck_3455_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3441_);
                                            crate::leanh::lean_inc(v_k_3440_);
                                            crate::leanh::lean_inc(v_size_3439_);
                                            crate::leanh::lean_dec(v___x_3338_);
                                            v___x_3443_ = crate::leanh::lean_box(0);
                                            v_isShared_3444_ = v_isSharedCheck_3455_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3458_ = crate::leanh::lean_ctor_get(v___x_3338_, 1);
                                        v_v_3459_ = crate::leanh::lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3471_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3471_ == 0 {
                                            v_unused_3472_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                            crate::leanh::lean_dec(v_unused_3472_);
                                            v_unused_3473_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                            crate::leanh::lean_dec(v_unused_3473_);
                                            v_unused_3474_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 0);
                                            crate::leanh::lean_dec(v_unused_3474_);
                                            v___x_3461_ = v___x_3338_;
                                            v_isShared_3462_ = v_isSharedCheck_3471_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3459_);
                                            crate::leanh::lean_inc(v_k_3458_);
                                            crate::leanh::lean_dec(v___x_3338_);
                                            v___x_3461_ = crate::leanh::lean_box(0);
                                            v_isShared_3462_ = v_isSharedCheck_3471_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3475_ = crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                    crate::leanh::lean_inc(v_r_3475_);
                                    if crate::leanh::lean_obj_tag(v_r_3475_) == 0 {
                                        v_k_3476_ = crate::leanh::lean_ctor_get(v___x_3338_, 1);
                                        v_v_3477_ = crate::leanh::lean_ctor_get(v___x_3338_, 2);
                                        v_isSharedCheck_3501_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3338_)) as u8;
                                        if v_isSharedCheck_3501_ == 0 {
                                            v_unused_3502_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 4);
                                            crate::leanh::lean_dec(v_unused_3502_);
                                            v_unused_3503_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 3);
                                            crate::leanh::lean_dec(v_unused_3503_);
                                            v_unused_3504_ =
                                                crate::leanh::lean_ctor_get(v___x_3338_, 0);
                                            crate::leanh::lean_dec(v_unused_3504_);
                                            v___x_3479_ = v___x_3338_;
                                            v_isShared_3480_ = v_isSharedCheck_3501_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3477_);
                                            crate::leanh::lean_inc(v_k_3476_);
                                            crate::leanh::lean_dec(v___x_3338_);
                                            v___x_3479_ = crate::leanh::lean_box(0);
                                            v_isShared_3480_ = v_isSharedCheck_3501_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_3505_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3336_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3335_, 4, v_r_3475_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3335_,
                                                3,
                                                v___x_3338_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3335_,
                                                0,
                                                v___x_3505_,
                                            );
                                            v___x_3507_ = v___x_3335_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3508_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3508_,
                                                0,
                                                v___x_3505_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3508_,
                                                1,
                                                v_k_3330_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3508_,
                                                2,
                                                v_v_3331_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3508_,
                                                3,
                                                v___x_3338_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3508_,
                                                4,
                                                v_r_3475_,
                                            );
                                            v___x_3507_ = v_reuseFailAlloc_3508_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3509_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3336_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3338_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3338_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3509_);
                                    v___x_3511_ = v___x_3335_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3512_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3512_,
                                        0,
                                        v___x_3509_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3512_,
                                        1,
                                        v_k_3330_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3512_,
                                        2,
                                        v_v_3331_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3512_,
                                        3,
                                        v___x_3338_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3512_,
                                        4,
                                        v___x_3338_,
                                    );
                                    v___x_3511_ = v_reuseFailAlloc_3512_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_3331_);
                        crate::leanh::lean_dec(v_k_3330_);
                        if v_isShared_3336_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3327_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3326_);
                            v___x_3514_ = v___x_3335_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_3515_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_size_3329_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 1, v_k_3326_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 2, v_v_3327_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 3, v_l_3332_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3515_, 4, v_r_3333_);
                            v___x_3514_ = v_reuseFailAlloc_3515_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_3329_);
                        v___x_3516_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(v_k_3326_, v_v_3327_, v_r_3333_);
                        if crate::leanh::lean_obj_tag(v_l_3332_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_3516_) == 0 {
                                v_size_3517_ = crate::leanh::lean_ctor_get(v_l_3332_, 0);
                                v_size_3518_ = crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                crate::leanh::lean_inc(v_size_3518_);
                                v_k_3519_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                                crate::leanh::lean_inc(v_k_3519_);
                                v_v_3520_ = crate::leanh::lean_ctor_get(v___x_3516_, 2);
                                crate::leanh::lean_inc(v_v_3520_);
                                v_l_3521_ = crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                crate::leanh::lean_inc(v_l_3521_);
                                v_r_3522_ = crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                crate::leanh::lean_inc(v_r_3522_);
                                v___x_3523_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3524_ = lean_nat_mul(v___x_3523_, v_size_3517_);
                                v___x_3525_ = lean_nat_dec_lt(v___x_3524_, v_size_3518_);
                                crate::leanh::lean_dec(v___x_3524_);
                                if v___x_3525_ == 0 {
                                    crate::leanh::lean_dec(v_r_3522_);
                                    crate::leanh::lean_dec(v_l_3521_);
                                    crate::leanh::lean_dec(v_v_3520_);
                                    crate::leanh::lean_dec(v_k_3519_);
                                    v___x_3526_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_3527_ = lean_nat_add(v___x_3526_, v_size_3517_);
                                    v___x_3528_ = lean_nat_add(v___x_3527_, v_size_3518_);
                                    crate::leanh::lean_dec(v_size_3518_);
                                    crate::leanh::lean_dec(v___x_3527_);
                                    if v_isShared_3336_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                        crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3528_);
                                        v___x_3530_ = v___x_3335_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3531_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            0,
                                            v___x_3528_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            1,
                                            v_k_3330_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            2,
                                            v_v_3331_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            3,
                                            v_l_3332_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3531_,
                                            4,
                                            v___x_3516_,
                                        );
                                        v___x_3530_ = v_reuseFailAlloc_3531_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_3601_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3516_)) as u8;
                                    if v_isSharedCheck_3601_ == 0 {
                                        v_unused_3602_ =
                                            crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                        crate::leanh::lean_dec(v_unused_3602_);
                                        v_unused_3603_ =
                                            crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                        crate::leanh::lean_dec(v_unused_3603_);
                                        v_unused_3604_ =
                                            crate::leanh::lean_ctor_get(v___x_3516_, 2);
                                        crate::leanh::lean_dec(v_unused_3604_);
                                        v_unused_3605_ =
                                            crate::leanh::lean_ctor_get(v___x_3516_, 1);
                                        crate::leanh::lean_dec(v_unused_3605_);
                                        v_unused_3606_ =
                                            crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                        crate::leanh::lean_dec(v_unused_3606_);
                                        v___x_3533_ = v___x_3516_;
                                        v_isShared_3534_ = v_isSharedCheck_3601_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3516_);
                                        v___x_3533_ = crate::leanh::lean_box(0);
                                        v_isShared_3534_ = v_isSharedCheck_3601_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3607_ = crate::leanh::lean_ctor_get(v_l_3332_, 0);
                                v___x_3608_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3609_ = lean_nat_add(v___x_3608_, v_size_3607_);
                                if v_isShared_3336_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3609_);
                                    v___x_3611_ = v___x_3335_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3612_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3612_,
                                        0,
                                        v___x_3609_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3612_,
                                        1,
                                        v_k_3330_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3612_,
                                        2,
                                        v_v_3331_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3612_,
                                        3,
                                        v_l_3332_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3612_,
                                        4,
                                        v___x_3516_,
                                    );
                                    v___x_3611_ = v_reuseFailAlloc_3612_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_3516_) == 0 {
                                v_l_3613_ = crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                crate::leanh::lean_inc(v_l_3613_);
                                if crate::leanh::lean_obj_tag(v_l_3613_) == 0 {
                                    v_r_3614_ = crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                    crate::leanh::lean_inc(v_r_3614_);
                                    if crate::leanh::lean_obj_tag(v_r_3614_) == 0 {
                                        v_size_3615_ = crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                        v_k_3616_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                                        v_v_3617_ = crate::leanh::lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3631_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3631_ == 0 {
                                            v_unused_3632_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                            crate::leanh::lean_dec(v_unused_3632_);
                                            v_unused_3633_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                            crate::leanh::lean_dec(v_unused_3633_);
                                            v___x_3619_ = v___x_3516_;
                                            v_isShared_3620_ = v_isSharedCheck_3631_;
                                            state = 40;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3617_);
                                            crate::leanh::lean_inc(v_k_3616_);
                                            crate::leanh::lean_inc(v_size_3615_);
                                            crate::leanh::lean_dec(v___x_3516_);
                                            v___x_3619_ = crate::leanh::lean_box(0);
                                            v_isShared_3620_ = v_isSharedCheck_3631_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_3634_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                                        v_v_3635_ = crate::leanh::lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3659_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3659_ == 0 {
                                            v_unused_3660_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                            crate::leanh::lean_dec(v_unused_3660_);
                                            v_unused_3661_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                            crate::leanh::lean_dec(v_unused_3661_);
                                            v_unused_3662_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                            crate::leanh::lean_dec(v_unused_3662_);
                                            v___x_3637_ = v___x_3516_;
                                            v_isShared_3638_ = v_isSharedCheck_3659_;
                                            state = 43;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3635_);
                                            crate::leanh::lean_inc(v_k_3634_);
                                            crate::leanh::lean_dec(v___x_3516_);
                                            v___x_3637_ = crate::leanh::lean_box(0);
                                            v_isShared_3638_ = v_isSharedCheck_3659_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3663_ = crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                    crate::leanh::lean_inc(v_r_3663_);
                                    if crate::leanh::lean_obj_tag(v_r_3663_) == 0 {
                                        v_k_3664_ = crate::leanh::lean_ctor_get(v___x_3516_, 1);
                                        v_v_3665_ = crate::leanh::lean_ctor_get(v___x_3516_, 2);
                                        v_isSharedCheck_3677_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3516_)) as u8;
                                        if v_isSharedCheck_3677_ == 0 {
                                            v_unused_3678_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 4);
                                            crate::leanh::lean_dec(v_unused_3678_);
                                            v_unused_3679_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 3);
                                            crate::leanh::lean_dec(v_unused_3679_);
                                            v_unused_3680_ =
                                                crate::leanh::lean_ctor_get(v___x_3516_, 0);
                                            crate::leanh::lean_dec(v_unused_3680_);
                                            v___x_3667_ = v___x_3516_;
                                            v_isShared_3668_ = v_isSharedCheck_3677_;
                                            state = 48;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3665_);
                                            crate::leanh::lean_inc(v_k_3664_);
                                            crate::leanh::lean_dec(v___x_3516_);
                                            v___x_3667_ = crate::leanh::lean_box(0);
                                            v_isShared_3668_ = v_isSharedCheck_3677_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_3681_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3336_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_3335_,
                                                4,
                                                v___x_3516_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_3335_, 3, v_r_3663_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3335_,
                                                0,
                                                v___x_3681_,
                                            );
                                            v___x_3683_ = v___x_3335_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3684_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3684_,
                                                0,
                                                v___x_3681_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3684_,
                                                1,
                                                v_k_3330_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3684_,
                                                2,
                                                v_v_3331_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3684_,
                                                3,
                                                v_r_3663_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3684_,
                                                4,
                                                v___x_3516_,
                                            );
                                            v___x_3683_ = v_reuseFailAlloc_3684_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_3685_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_3336_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3516_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3516_);
                                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3685_);
                                    v___x_3687_ = v___x_3335_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3688_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3688_,
                                        0,
                                        v___x_3685_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3688_,
                                        1,
                                        v_k_3330_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3688_,
                                        2,
                                        v_v_3331_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3688_,
                                        3,
                                        v___x_3516_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3688_,
                                        4,
                                        v___x_3516_,
                                    );
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
                if crate::leanh::lean_obj_tag(v_l_3343_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_3344_) == 0 {
                        v_size_3357_ = crate::leanh::lean_ctor_get(v_l_3343_, 0);
                        v_size_3358_ = crate::leanh::lean_ctor_get(v_r_3344_, 0);
                        v_k_3359_ = crate::leanh::lean_ctor_get(v_r_3344_, 1);
                        v_v_3360_ = crate::leanh::lean_ctor_get(v_r_3344_, 2);
                        v_l_3361_ = crate::leanh::lean_ctor_get(v_r_3344_, 3);
                        v_r_3362_ = crate::leanh::lean_ctor_get(v_r_3344_, 4);
                        v___x_3363_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3364_ = lean_nat_mul(v___x_3363_, v_size_3357_);
                        v___x_3365_ = lean_nat_dec_lt(v_size_3358_, v___x_3364_);
                        crate::leanh::lean_dec(v___x_3364_);
                        if v___x_3365_ == 0 {
                            crate::leanh::lean_inc(v_r_3362_);
                            crate::leanh::lean_inc(v_l_3361_);
                            crate::leanh::lean_inc(v_v_3360_);
                            crate::leanh::lean_inc(v_k_3359_);
                            v_isSharedCheck_3395_ =
                                (!crate::leanh::lean_is_exclusive(v_r_3344_)) as u8;
                            if v_isSharedCheck_3395_ == 0 {
                                v_unused_3396_ = crate::leanh::lean_ctor_get(v_r_3344_, 4);
                                crate::leanh::lean_dec(v_unused_3396_);
                                v_unused_3397_ = crate::leanh::lean_ctor_get(v_r_3344_, 3);
                                crate::leanh::lean_dec(v_unused_3397_);
                                v_unused_3398_ = crate::leanh::lean_ctor_get(v_r_3344_, 2);
                                crate::leanh::lean_dec(v_unused_3398_);
                                v_unused_3399_ = crate::leanh::lean_ctor_get(v_r_3344_, 1);
                                crate::leanh::lean_dec(v_unused_3399_);
                                v_unused_3400_ = crate::leanh::lean_ctor_get(v_r_3344_, 0);
                                crate::leanh::lean_dec(v_unused_3400_);
                                v___x_3367_ = v_r_3344_;
                                v_isShared_3368_ = v_isSharedCheck_3395_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_3344_);
                                v___x_3367_ = crate::leanh::lean_box(0);
                                v_isShared_3368_ = v_isSharedCheck_3395_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3335_);
                            v___x_3401_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3402_ = lean_nat_add(v___x_3401_, v_size_3340_);
                            crate::leanh::lean_dec(v_size_3340_);
                            v___x_3403_ = lean_nat_add(v___x_3402_, v_size_3339_);
                            crate::leanh::lean_dec(v___x_3402_);
                            v___x_3404_ = lean_nat_add(v___x_3401_, v_size_3339_);
                            v___x_3405_ = lean_nat_add(v___x_3404_, v_size_3358_);
                            crate::leanh::lean_dec(v___x_3404_);
                            crate::leanh::lean_inc_ref(v_r_3333_);
                            if v_isShared_3356_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3355_, 4, v_r_3333_);
                                crate::leanh::lean_ctor_set(v___x_3355_, 3, v_r_3344_);
                                crate::leanh::lean_ctor_set(v___x_3355_, 2, v_v_3331_);
                                crate::leanh::lean_ctor_set(v___x_3355_, 1, v_k_3330_);
                                crate::leanh::lean_ctor_set(v___x_3355_, 0, v___x_3405_);
                                v___x_3407_ = v___x_3355_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_3420_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3405_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 1, v_k_3330_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 2, v_v_3331_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 3, v_r_3344_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 4, v_r_3333_);
                                v___x_3407_ = v_reuseFailAlloc_3420_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_3343_, 5);
                        crate::leanh::lean_del_object(v___x_3355_);
                        crate::leanh::lean_dec(v_v_3342_);
                        crate::leanh::lean_dec(v_k_3341_);
                        crate::leanh::lean_dec(v_size_3340_);
                        crate::leanh::lean_dec_ref_known(v_r_3333_, 5);
                        crate::leanh::lean_del_object(v___x_3335_);
                        crate::leanh::lean_dec(v_v_3331_);
                        crate::leanh::lean_dec(v_k_3330_);
                        v___x_3421_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__3);
                        v___x_3422_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3421_);
                        return v___x_3422_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3355_);
                    crate::leanh::lean_dec(v_r_3344_);
                    crate::leanh::lean_dec(v_v_3342_);
                    crate::leanh::lean_dec(v_k_3341_);
                    crate::leanh::lean_dec(v_size_3340_);
                    crate::leanh::lean_dec_ref_known(v_r_3333_, 5);
                    crate::leanh::lean_del_object(v___x_3335_);
                    crate::leanh::lean_dec(v_v_3331_);
                    crate::leanh::lean_dec(v_k_3330_);
                    v___x_3423_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__4);
                    v___x_3424_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3423_);
                    return v___x_3424_;
                }
            }
            4 => {
                v___x_3369_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3370_ = lean_nat_add(v___x_3369_, v_size_3340_);
                crate::leanh::lean_dec(v_size_3340_);
                v___x_3371_ = lean_nat_add(v___x_3370_, v_size_3339_);
                crate::leanh::lean_dec(v___x_3370_);
                v___x_3383_ = lean_nat_add(v___x_3369_, v_size_3357_);
                if crate::leanh::lean_obj_tag(v_l_3361_) == 0 {
                    v_size_3393_ = crate::leanh::lean_ctor_get(v_l_3361_, 0);
                    crate::leanh::lean_inc(v_size_3393_);
                    v___y_3385_ = v_size_3393_;
                    state = 8;
                    continue;
                } else {
                    v___x_3394_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3385_ = v___x_3394_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3376_ = lean_nat_add(v___y_3374_, v___y_3375_);
                crate::leanh::lean_dec(v___y_3375_);
                crate::leanh::lean_dec(v___y_3374_);
                if v_isShared_3368_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3367_, 4, v_r_3333_);
                    crate::leanh::lean_ctor_set(v___x_3367_, 3, v_r_3362_);
                    crate::leanh::lean_ctor_set(v___x_3367_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3367_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3367_, 0, v___x_3376_);
                    v___x_3378_ = v___x_3367_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3376_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_r_3362_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 4, v_r_3333_);
                    v___x_3378_ = v_reuseFailAlloc_3382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3356_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3355_, 4, v___x_3378_);
                    crate::leanh::lean_ctor_set(v___x_3355_, 3, v___y_3373_);
                    crate::leanh::lean_ctor_set(v___x_3355_, 2, v_v_3360_);
                    crate::leanh::lean_ctor_set(v___x_3355_, 1, v_k_3359_);
                    crate::leanh::lean_ctor_set(v___x_3355_, 0, v___x_3371_);
                    v___x_3380_ = v___x_3355_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 1, v_k_3359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 2, v_v_3360_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 3, v___y_3373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 4, v___x_3378_);
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
                crate::leanh::lean_dec(v___y_3385_);
                crate::leanh::lean_dec(v___x_3383_);
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v_l_3361_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v_l_3343_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3342_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3341_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3386_);
                    v___x_3388_ = v___x_3335_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3392_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_k_3341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_v_3342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_l_3343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3392_, 4, v_l_3361_);
                    v___x_3388_ = v_reuseFailAlloc_3392_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3389_ = lean_nat_add(v___x_3369_, v_size_3339_);
                if crate::leanh::lean_obj_tag(v_r_3362_) == 0 {
                    v_size_3390_ = crate::leanh::lean_ctor_get(v_r_3362_, 0);
                    crate::leanh::lean_inc(v_size_3390_);
                    v___y_3373_ = v___x_3388_;
                    v___y_3374_ = v___x_3389_;
                    v___y_3375_ = v_size_3390_;
                    state = 5;
                    continue;
                } else {
                    v___x_3391_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3373_ = v___x_3388_;
                    v___y_3374_ = v___x_3389_;
                    v___y_3375_ = v___x_3391_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3414_ = (!crate::leanh::lean_is_exclusive(v_r_3333_)) as u8;
                if v_isSharedCheck_3414_ == 0 {
                    v_unused_3415_ = crate::leanh::lean_ctor_get(v_r_3333_, 4);
                    crate::leanh::lean_dec(v_unused_3415_);
                    v_unused_3416_ = crate::leanh::lean_ctor_get(v_r_3333_, 3);
                    crate::leanh::lean_dec(v_unused_3416_);
                    v_unused_3417_ = crate::leanh::lean_ctor_get(v_r_3333_, 2);
                    crate::leanh::lean_dec(v_unused_3417_);
                    v_unused_3418_ = crate::leanh::lean_ctor_get(v_r_3333_, 1);
                    crate::leanh::lean_dec(v_unused_3418_);
                    v_unused_3419_ = crate::leanh::lean_ctor_get(v_r_3333_, 0);
                    crate::leanh::lean_dec(v_unused_3419_);
                    v___x_3409_ = v_r_3333_;
                    v_isShared_3410_ = v_isSharedCheck_3414_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_3333_);
                    v___x_3409_ = crate::leanh::lean_box(0);
                    v_isShared_3410_ = v_isSharedCheck_3414_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3410_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3409_, 4, v___x_3407_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 3, v_l_3343_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 2, v_v_3342_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 1, v_k_3341_);
                    crate::leanh::lean_ctor_set(v___x_3409_, 0, v___x_3403_);
                    v___x_3412_ = v___x_3409_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3413_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3403_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 1, v_k_3341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 2, v_v_3342_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 3, v_l_3343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3413_, 4, v___x_3407_);
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
                v_size_3445_ = crate::leanh::lean_ctor_get(v_r_3438_, 0);
                v___x_3446_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3447_ = lean_nat_add(v___x_3446_, v_size_3439_);
                crate::leanh::lean_dec(v_size_3439_);
                v___x_3448_ = lean_nat_add(v___x_3446_, v_size_3445_);
                if v_isShared_3444_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3443_, 4, v_r_3333_);
                    crate::leanh::lean_ctor_set(v___x_3443_, 3, v_r_3438_);
                    crate::leanh::lean_ctor_set(v___x_3443_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3443_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3443_, 0, v___x_3448_);
                    v___x_3450_ = v___x_3443_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3454_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 0, v___x_3448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 3, v_r_3438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3454_, 4, v_r_3333_);
                    v___x_3450_ = v_reuseFailAlloc_3454_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3450_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3441_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3440_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3447_);
                    v___x_3452_ = v___x_3335_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3453_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 1, v_k_3440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 2, v_v_3441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3453_, 4, v___x_3450_);
                    v___x_3452_ = v_reuseFailAlloc_3453_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3452_;
            }
            17 => {
                v___x_3463_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3464_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3462_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3461_, 3, v_r_3438_);
                    crate::leanh::lean_ctor_set(v___x_3461_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3461_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3461_, 0, v___x_3464_);
                    v___x_3466_ = v___x_3461_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3470_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 0, v___x_3464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 3, v_r_3438_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3470_, 4, v_r_3438_);
                    v___x_3466_ = v_reuseFailAlloc_3470_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3466_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3459_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3458_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3463_);
                    v___x_3468_ = v___x_3335_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3469_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_k_3458_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 2, v_v_3459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3469_, 4, v___x_3466_);
                    v___x_3468_ = v_reuseFailAlloc_3469_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3468_;
            }
            20 => {
                v_k_3481_ = crate::leanh::lean_ctor_get(v_r_3475_, 1);
                v_v_3482_ = crate::leanh::lean_ctor_get(v_r_3475_, 2);
                v_isSharedCheck_3497_ = (!crate::leanh::lean_is_exclusive(v_r_3475_)) as u8;
                if v_isSharedCheck_3497_ == 0 {
                    v_unused_3498_ = crate::leanh::lean_ctor_get(v_r_3475_, 4);
                    crate::leanh::lean_dec(v_unused_3498_);
                    v_unused_3499_ = crate::leanh::lean_ctor_get(v_r_3475_, 3);
                    crate::leanh::lean_dec(v_unused_3499_);
                    v_unused_3500_ = crate::leanh::lean_ctor_get(v_r_3475_, 0);
                    crate::leanh::lean_dec(v_unused_3500_);
                    v___x_3484_ = v_r_3475_;
                    v_isShared_3485_ = v_isSharedCheck_3497_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3482_);
                    crate::leanh::lean_inc(v_k_3481_);
                    crate::leanh::lean_dec(v_r_3475_);
                    v___x_3484_ = crate::leanh::lean_box(0);
                    v_isShared_3485_ = v_isSharedCheck_3497_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3486_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3487_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3484_, 4, v_l_3437_);
                    crate::leanh::lean_ctor_set(v___x_3484_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v___x_3484_, 2, v_v_3477_);
                    crate::leanh::lean_ctor_set(v___x_3484_, 1, v_k_3476_);
                    crate::leanh::lean_ctor_set(v___x_3484_, 0, v___x_3487_);
                    v___x_3489_ = v___x_3484_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3496_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 0, v___x_3487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 1, v_k_3476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 2, v_v_3477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3496_, 4, v_l_3437_);
                    v___x_3489_ = v_reuseFailAlloc_3496_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_3480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3479_, 4, v_l_3437_);
                    crate::leanh::lean_ctor_set(v___x_3479_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3479_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3479_, 0, v___x_3487_);
                    v___x_3491_ = v___x_3479_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3495_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 3, v_l_3437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3495_, 4, v_l_3437_);
                    v___x_3491_ = v_reuseFailAlloc_3495_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3491_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3489_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3482_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3481_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3486_);
                    v___x_3493_ = v___x_3335_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3494_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 0, v___x_3486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_k_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 2, v_v_3482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 3, v___x_3489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3494_, 4, v___x_3491_);
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
                if crate::leanh::lean_obj_tag(v_l_3521_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_3522_) == 0 {
                        v_size_3535_ = crate::leanh::lean_ctor_get(v_l_3521_, 0);
                        v_k_3536_ = crate::leanh::lean_ctor_get(v_l_3521_, 1);
                        v_v_3537_ = crate::leanh::lean_ctor_get(v_l_3521_, 2);
                        v_l_3538_ = crate::leanh::lean_ctor_get(v_l_3521_, 3);
                        v_r_3539_ = crate::leanh::lean_ctor_get(v_l_3521_, 4);
                        v_size_3540_ = crate::leanh::lean_ctor_get(v_r_3522_, 0);
                        v___x_3541_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_3542_ = lean_nat_mul(v___x_3541_, v_size_3540_);
                        v___x_3543_ = lean_nat_dec_lt(v_size_3535_, v___x_3542_);
                        crate::leanh::lean_dec(v___x_3542_);
                        if v___x_3543_ == 0 {
                            crate::leanh::lean_inc(v_r_3539_);
                            crate::leanh::lean_inc(v_l_3538_);
                            crate::leanh::lean_inc(v_v_3537_);
                            crate::leanh::lean_inc(v_k_3536_);
                            v_isSharedCheck_3572_ =
                                (!crate::leanh::lean_is_exclusive(v_l_3521_)) as u8;
                            if v_isSharedCheck_3572_ == 0 {
                                v_unused_3573_ = crate::leanh::lean_ctor_get(v_l_3521_, 4);
                                crate::leanh::lean_dec(v_unused_3573_);
                                v_unused_3574_ = crate::leanh::lean_ctor_get(v_l_3521_, 3);
                                crate::leanh::lean_dec(v_unused_3574_);
                                v_unused_3575_ = crate::leanh::lean_ctor_get(v_l_3521_, 2);
                                crate::leanh::lean_dec(v_unused_3575_);
                                v_unused_3576_ = crate::leanh::lean_ctor_get(v_l_3521_, 1);
                                crate::leanh::lean_dec(v_unused_3576_);
                                v_unused_3577_ = crate::leanh::lean_ctor_get(v_l_3521_, 0);
                                crate::leanh::lean_dec(v_unused_3577_);
                                v___x_3545_ = v_l_3521_;
                                v_isShared_3546_ = v_isSharedCheck_3572_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_3521_);
                                v___x_3545_ = crate::leanh::lean_box(0);
                                v_isShared_3546_ = v_isSharedCheck_3572_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_3335_);
                            v___x_3578_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_3579_ = lean_nat_add(v___x_3578_, v_size_3517_);
                            v___x_3580_ = lean_nat_add(v___x_3579_, v_size_3518_);
                            crate::leanh::lean_dec(v_size_3518_);
                            v___x_3581_ = lean_nat_add(v___x_3579_, v_size_3535_);
                            crate::leanh::lean_dec(v___x_3579_);
                            crate::leanh::lean_inc_ref(v_l_3332_);
                            if v_isShared_3534_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3533_, 4, v_l_3521_);
                                crate::leanh::lean_ctor_set(v___x_3533_, 3, v_l_3332_);
                                crate::leanh::lean_ctor_set(v___x_3533_, 2, v_v_3331_);
                                crate::leanh::lean_ctor_set(v___x_3533_, 1, v_k_3330_);
                                crate::leanh::lean_ctor_set(v___x_3533_, 0, v___x_3581_);
                                v___x_3583_ = v___x_3533_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_3596_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3581_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_k_3330_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 2, v_v_3331_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 3, v_l_3332_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 4, v_l_3521_);
                                v___x_3583_ = v_reuseFailAlloc_3596_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_3521_, 5);
                        crate::leanh::lean_del_object(v___x_3533_);
                        crate::leanh::lean_dec(v_v_3520_);
                        crate::leanh::lean_dec(v_k_3519_);
                        crate::leanh::lean_dec(v_size_3518_);
                        crate::leanh::lean_dec_ref_known(v_l_3332_, 5);
                        crate::leanh::lean_del_object(v___x_3335_);
                        crate::leanh::lean_dec(v_v_3331_);
                        crate::leanh::lean_dec(v_k_3330_);
                        v___x_3597_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__7);
                        v___x_3598_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3597_);
                        return v___x_3598_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3533_);
                    crate::leanh::lean_dec(v_r_3522_);
                    crate::leanh::lean_dec(v_v_3520_);
                    crate::leanh::lean_dec(v_k_3519_);
                    crate::leanh::lean_dec(v_size_3518_);
                    crate::leanh::lean_dec_ref_known(v_l_3332_, 5);
                    crate::leanh::lean_del_object(v___x_3335_);
                    crate::leanh::lean_dec(v_v_3331_);
                    crate::leanh::lean_dec(v_k_3330_);
                    v___x_3599_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg___closed__8);
                    v___x_3600_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v___x_3599_);
                    return v___x_3600_;
                }
            }
            30 => {
                v___x_3547_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3548_ = lean_nat_add(v___x_3547_, v_size_3517_);
                v___x_3549_ = lean_nat_add(v___x_3548_, v_size_3518_);
                crate::leanh::lean_dec(v_size_3518_);
                if crate::leanh::lean_obj_tag(v_l_3538_) == 0 {
                    v_size_3570_ = crate::leanh::lean_ctor_get(v_l_3538_, 0);
                    crate::leanh::lean_inc(v_size_3570_);
                    v___y_3562_ = v_size_3570_;
                    state = 34;
                    continue;
                } else {
                    v___x_3571_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3562_ = v___x_3571_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_3554_ = lean_nat_add(v___y_3552_, v___y_3553_);
                crate::leanh::lean_dec(v___y_3553_);
                crate::leanh::lean_dec(v___y_3552_);
                if v_isShared_3546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3545_, 4, v_r_3522_);
                    crate::leanh::lean_ctor_set(v___x_3545_, 3, v_r_3539_);
                    crate::leanh::lean_ctor_set(v___x_3545_, 2, v_v_3520_);
                    crate::leanh::lean_ctor_set(v___x_3545_, 1, v_k_3519_);
                    crate::leanh::lean_ctor_set(v___x_3545_, 0, v___x_3554_);
                    v___x_3556_ = v___x_3545_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3554_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_k_3519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_v_3520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_r_3539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_r_3522_);
                    v___x_3556_ = v_reuseFailAlloc_3560_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_3534_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3533_, 4, v___x_3556_);
                    crate::leanh::lean_ctor_set(v___x_3533_, 3, v___y_3551_);
                    crate::leanh::lean_ctor_set(v___x_3533_, 2, v_v_3537_);
                    crate::leanh::lean_ctor_set(v___x_3533_, 1, v_k_3536_);
                    crate::leanh::lean_ctor_set(v___x_3533_, 0, v___x_3549_);
                    v___x_3558_ = v___x_3533_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3559_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 1, v_k_3536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 2, v_v_3537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 3, v___y_3551_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3559_, 4, v___x_3556_);
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
                crate::leanh::lean_dec(v___y_3562_);
                crate::leanh::lean_dec(v___x_3548_);
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v_l_3538_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3563_);
                    v___x_3565_ = v___x_3335_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v___x_3563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 3, v_l_3332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 4, v_l_3538_);
                    v___x_3565_ = v_reuseFailAlloc_3569_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_3566_ = lean_nat_add(v___x_3547_, v_size_3540_);
                if crate::leanh::lean_obj_tag(v_r_3539_) == 0 {
                    v_size_3567_ = crate::leanh::lean_ctor_get(v_r_3539_, 0);
                    crate::leanh::lean_inc(v_size_3567_);
                    v___y_3551_ = v___x_3565_;
                    v___y_3552_ = v___x_3566_;
                    v___y_3553_ = v_size_3567_;
                    state = 31;
                    continue;
                } else {
                    v___x_3568_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3551_ = v___x_3565_;
                    v___y_3552_ = v___x_3566_;
                    v___y_3553_ = v___x_3568_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_3590_ = (!crate::leanh::lean_is_exclusive(v_l_3332_)) as u8;
                if v_isSharedCheck_3590_ == 0 {
                    v_unused_3591_ = crate::leanh::lean_ctor_get(v_l_3332_, 4);
                    crate::leanh::lean_dec(v_unused_3591_);
                    v_unused_3592_ = crate::leanh::lean_ctor_get(v_l_3332_, 3);
                    crate::leanh::lean_dec(v_unused_3592_);
                    v_unused_3593_ = crate::leanh::lean_ctor_get(v_l_3332_, 2);
                    crate::leanh::lean_dec(v_unused_3593_);
                    v_unused_3594_ = crate::leanh::lean_ctor_get(v_l_3332_, 1);
                    crate::leanh::lean_dec(v_unused_3594_);
                    v_unused_3595_ = crate::leanh::lean_ctor_get(v_l_3332_, 0);
                    crate::leanh::lean_dec(v_unused_3595_);
                    v___x_3585_ = v_l_3332_;
                    v_isShared_3586_ = v_isSharedCheck_3590_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_3332_);
                    v___x_3585_ = crate::leanh::lean_box(0);
                    v_isShared_3586_ = v_isSharedCheck_3590_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_3586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3585_, 4, v_r_3522_);
                    crate::leanh::lean_ctor_set(v___x_3585_, 3, v___x_3583_);
                    crate::leanh::lean_ctor_set(v___x_3585_, 2, v_v_3520_);
                    crate::leanh::lean_ctor_set(v___x_3585_, 1, v_k_3519_);
                    crate::leanh::lean_ctor_set(v___x_3585_, 0, v___x_3580_);
                    v___x_3588_ = v___x_3585_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3589_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_k_3519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 2, v_v_3520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 3, v___x_3583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3589_, 4, v_r_3522_);
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
                v_size_3621_ = crate::leanh::lean_ctor_get(v_l_3613_, 0);
                v___x_3622_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3623_ = lean_nat_add(v___x_3622_, v_size_3615_);
                crate::leanh::lean_dec(v_size_3615_);
                v___x_3624_ = lean_nat_add(v___x_3622_, v_size_3621_);
                if v_isShared_3620_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3619_, 4, v_l_3613_);
                    crate::leanh::lean_ctor_set(v___x_3619_, 3, v_l_3332_);
                    crate::leanh::lean_ctor_set(v___x_3619_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3619_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3619_, 0, v___x_3624_);
                    v___x_3626_ = v___x_3619_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 4, v_l_3613_);
                    v___x_3626_ = v_reuseFailAlloc_3630_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v_r_3614_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3626_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3617_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3616_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3623_);
                    v___x_3628_ = v___x_3335_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3629_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 1, v_k_3616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 2, v_v_3617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 3, v___x_3626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3629_, 4, v_r_3614_);
                    v___x_3628_ = v_reuseFailAlloc_3629_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3628_;
            }
            43 => {
                v_k_3639_ = crate::leanh::lean_ctor_get(v_l_3613_, 1);
                v_v_3640_ = crate::leanh::lean_ctor_get(v_l_3613_, 2);
                v_isSharedCheck_3655_ = (!crate::leanh::lean_is_exclusive(v_l_3613_)) as u8;
                if v_isSharedCheck_3655_ == 0 {
                    v_unused_3656_ = crate::leanh::lean_ctor_get(v_l_3613_, 4);
                    crate::leanh::lean_dec(v_unused_3656_);
                    v_unused_3657_ = crate::leanh::lean_ctor_get(v_l_3613_, 3);
                    crate::leanh::lean_dec(v_unused_3657_);
                    v_unused_3658_ = crate::leanh::lean_ctor_get(v_l_3613_, 0);
                    crate::leanh::lean_dec(v_unused_3658_);
                    v___x_3642_ = v_l_3613_;
                    v_isShared_3643_ = v_isSharedCheck_3655_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3640_);
                    crate::leanh::lean_inc(v_k_3639_);
                    crate::leanh::lean_dec(v_l_3613_);
                    v___x_3642_ = crate::leanh::lean_box(0);
                    v_isShared_3643_ = v_isSharedCheck_3655_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_3644_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3645_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3642_, 4, v_r_3614_);
                    crate::leanh::lean_ctor_set(v___x_3642_, 3, v_r_3614_);
                    crate::leanh::lean_ctor_set(v___x_3642_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3642_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3642_, 0, v___x_3645_);
                    v___x_3647_ = v___x_3642_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3654_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 3, v_r_3614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3654_, 4, v_r_3614_);
                    v___x_3647_ = v_reuseFailAlloc_3654_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3637_, 3, v_r_3614_);
                    crate::leanh::lean_ctor_set(v___x_3637_, 0, v___x_3645_);
                    v___x_3649_ = v___x_3637_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3653_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 1, v_k_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 2, v_v_3635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 3, v_r_3614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3653_, 4, v_r_3614_);
                    v___x_3649_ = v_reuseFailAlloc_3653_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v___x_3649_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3647_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3640_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3639_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3644_);
                    v___x_3651_ = v___x_3335_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_k_3639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_v_3640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 3, v___x_3647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 4, v___x_3649_);
                    v___x_3651_ = v_reuseFailAlloc_3652_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3651_;
            }
            48 => {
                v___x_3669_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3670_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_3668_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3667_, 4, v_l_3613_);
                    crate::leanh::lean_ctor_set(v___x_3667_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v___x_3667_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v___x_3667_, 0, v___x_3670_);
                    v___x_3672_ = v___x_3667_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3676_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_k_3330_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 2, v_v_3331_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 3, v_l_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3676_, 4, v_l_3613_);
                    v___x_3672_ = v_reuseFailAlloc_3676_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 4, v_r_3663_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v___x_3672_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3665_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3664_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3669_);
                    v___x_3674_ = v___x_3335_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_k_3664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 2, v_v_3665_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 3, v___x_3672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 4, v_r_3663_);
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
pub unsafe fn _init_l_Lean_Json_setObjVal_x21___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3694_ = l_Lean_Json_setObjVal_x21___closed__1;
    v___x_3695_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_3696_ = crate::leanh::lean_unsigned_to_nat(285);
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
    mut v_x_3700_: *mut crate::leanh::LeanObject,
    mut v_x_3701_: *mut crate::leanh::LeanObject,
    mut v_x_3702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kvPairs_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3706_: u8 = 0;
    let mut v___x_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3711_: u8 = 0;
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3700_) == 5 {
                    v_kvPairs_3703_ = crate::leanh::lean_ctor_get(v_x_3700_, 0);
                    v_isSharedCheck_3711_ = (!crate::leanh::lean_is_exclusive(v_x_3700_)) as u8;
                    if v_isSharedCheck_3711_ == 0 {
                        v___x_3705_ = v_x_3700_;
                        v_isShared_3706_ = v_isSharedCheck_3711_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_kvPairs_3703_);
                        crate::leanh::lean_dec(v_x_3700_);
                        v___x_3705_ = crate::leanh::lean_box(0);
                        v_isShared_3706_ = v_isSharedCheck_3711_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3702_);
                    crate::leanh::lean_dec_ref(v_x_3701_);
                    crate::leanh::lean_dec(v_x_3700_);
                    v___x_3712_ = crate::leanh::lean_obj_once(
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
                    crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3707_);
                    v___x_3709_ = v___x_3705_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3710_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3710_, 0, v___x_3707_);
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
    mut v_00_u03b2_3714_: *mut crate::leanh::LeanObject,
    mut v_msg_3715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3716_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0_spec__0___redArg(v_msg_3715_);
    return v___x_3716_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0(
    mut v_00_u03b2_3717_: *mut crate::leanh::LeanObject,
    mut v_k_3718_: *mut crate::leanh::LeanObject,
    mut v_v_3719_: *mut crate::leanh::LeanObject,
    mut v_t_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ =
        l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lean_Json_setObjVal_x21_spec__0___redArg(
            v_k_3718_, v_v_3719_, v_t_3720_,
        );
    return v___x_3721_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(
    mut v_init_3722_: *mut crate::leanh::LeanObject,
    mut v_x_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3723_) == 0 {
                    v_k_3724_ = crate::leanh::lean_ctor_get(v_x_3723_, 1);
                    crate::leanh::lean_inc(v_k_3724_);
                    v_v_3725_ = crate::leanh::lean_ctor_get(v_x_3723_, 2);
                    crate::leanh::lean_inc(v_v_3725_);
                    v_l_3726_ = crate::leanh::lean_ctor_get(v_x_3723_, 3);
                    crate::leanh::lean_inc(v_l_3726_);
                    v_r_3727_ = crate::leanh::lean_ctor_get(v_x_3723_, 4);
                    crate::leanh::lean_inc(v_r_3727_);
                    crate::leanh::lean_dec_ref_known(v_x_3723_, 5);
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
    mut v_x_3731_: *mut crate::leanh::LeanObject,
    mut v_x_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kvPairs_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kvPairs_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3737_: u8 = 0;
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3742_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3731_) == 5 {
                    if crate::leanh::lean_obj_tag(v_x_3732_) == 5 {
                        v_kvPairs_3733_ = crate::leanh::lean_ctor_get(v_x_3731_, 0);
                        crate::leanh::lean_inc(v_kvPairs_3733_);
                        crate::leanh::lean_dec_ref_known(v_x_3731_, 1);
                        v_kvPairs_3734_ = crate::leanh::lean_ctor_get(v_x_3732_, 0);
                        v_isSharedCheck_3742_ = (!crate::leanh::lean_is_exclusive(v_x_3732_)) as u8;
                        if v_isSharedCheck_3742_ == 0 {
                            v___x_3736_ = v_x_3732_;
                            v_isShared_3737_ = v_isSharedCheck_3742_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_kvPairs_3734_);
                            crate::leanh::lean_dec(v_x_3732_);
                            v___x_3736_ = crate::leanh::lean_box(0);
                            v_isShared_3737_ = v_isSharedCheck_3742_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_x_3731_, 1);
                        return v_x_3732_;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_3731_);
                    return v_x_3732_;
                }
            }
            1 => {
                v___x_3738_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_kvPairs_3733_, v_kvPairs_3734_);
                if v_isShared_3737_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3736_, 0, v___x_3738_);
                    v___x_3740_ = v___x_3736_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3741_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3741_, 0, v___x_3738_);
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
    mut v_init_3743_: *mut crate::leanh::LeanObject,
    mut v_t_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3745_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Json_mergeObj_spec__0_spec__0(v_init_3743_, v_t_3744_);
    return v___x_3745_;
}
pub unsafe fn l_Lean_Json_Structured_ctorIdx(
    mut v_x_3746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3746_) == 0 {
        let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3747_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_3747_;
    } else {
        let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3748_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_3748_;
    }
}
pub unsafe fn l_Lean_Json_Structured_ctorIdx___boxed(
    mut v_x_3749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3750_ = l_Lean_Json_Structured_ctorIdx(v_x_3749_);
    crate::leanh::lean_dec_ref(v_x_3749_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Json_Structured_ctorElim___redArg(
    mut v_t_3751_: *mut crate::leanh::LeanObject,
    mut v_k_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_3751_) == 0 {
        let mut v_elems_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_elems_3753_ = crate::leanh::lean_ctor_get(v_t_3751_, 0);
        crate::leanh::lean_inc_ref(v_elems_3753_);
        crate::leanh::lean_dec_ref_known(v_t_3751_, 1);
        v___x_3754_ = crate::leanh::lean_apply_1(v_k_3752_, v_elems_3753_);
        return v___x_3754_;
    } else {
        let mut v_kvPairs_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_kvPairs_3755_ = crate::leanh::lean_ctor_get(v_t_3751_, 0);
        crate::leanh::lean_inc(v_kvPairs_3755_);
        crate::leanh::lean_dec_ref_known(v_t_3751_, 1);
        v___x_3756_ = crate::leanh::lean_apply_1(v_k_3752_, v_kvPairs_3755_);
        return v___x_3756_;
    }
}
pub unsafe fn l_Lean_Json_Structured_ctorElim(
    mut v_motive_3757_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3758_: *mut crate::leanh::LeanObject,
    mut v_t_3759_: *mut crate::leanh::LeanObject,
    mut v_h_3760_: *mut crate::leanh::LeanObject,
    mut v_k_3761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3762_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3759_, v_k_3761_);
    return v___x_3762_;
}
pub unsafe fn l_Lean_Json_Structured_ctorElim___boxed(
    mut v_motive_3763_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_3764_: *mut crate::leanh::LeanObject,
    mut v_t_3765_: *mut crate::leanh::LeanObject,
    mut v_h_3766_: *mut crate::leanh::LeanObject,
    mut v_k_3767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3768_ = l_Lean_Json_Structured_ctorElim(
        v_motive_3763_,
        v_ctorIdx_3764_,
        v_t_3765_,
        v_h_3766_,
        v_k_3767_,
    );
    crate::leanh::lean_dec(v_ctorIdx_3764_);
    return v_res_3768_;
}
pub unsafe fn l_Lean_Json_Structured_arr_elim___redArg(
    mut v_t_3769_: *mut crate::leanh::LeanObject,
    mut v_arr_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3771_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3769_, v_arr_3770_);
    return v___x_3771_;
}
pub unsafe fn l_Lean_Json_Structured_arr_elim(
    mut v_motive_3772_: *mut crate::leanh::LeanObject,
    mut v_t_3773_: *mut crate::leanh::LeanObject,
    mut v_h_3774_: *mut crate::leanh::LeanObject,
    mut v_arr_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3773_, v_arr_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Lean_Json_Structured_obj_elim___redArg(
    mut v_t_3777_: *mut crate::leanh::LeanObject,
    mut v_obj_3778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3779_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3777_, v_obj_3778_);
    return v___x_3779_;
}
pub unsafe fn l_Lean_Json_Structured_obj_elim(
    mut v_motive_3780_: *mut crate::leanh::LeanObject,
    mut v_t_3781_: *mut crate::leanh::LeanObject,
    mut v_h_3782_: *mut crate::leanh::LeanObject,
    mut v_obj_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3784_ = l_Lean_Json_Structured_ctorElim___redArg(v_t_3781_, v_obj_3783_);
    return v___x_3784_;
}
pub unsafe fn l_Lean_Json_instCoeArrayStructured___lam__0(
    mut v_elems_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3786_, 0, v_elems_3785_);
    return v___x_3786_;
}
pub unsafe fn l_Lean_Json_instCoeRawStringStructured___lam__0(
    mut v_kvPairs_3789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3790_, 0, v_kvPairs_3789_);
    return v___x_3790_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_JsonNumber_ltProp = _init_l_Lean_JsonNumber_ltProp();
    crate::leanh::lean_mark_persistent(l_Lean_JsonNumber_ltProp);
    l_Lean_JsonNumber_instInhabited = _init_l_Lean_JsonNumber_instInhabited();
    crate::leanh::lean_mark_persistent(l_Lean_JsonNumber_instInhabited);
    l_Lean_instInhabitedJson_default = _init_l_Lean_instInhabitedJson_default();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedJson_default);
    l_Lean_instInhabitedJson = _init_l_Lean_instInhabitedJson();
    crate::leanh::lean_mark_persistent(l_Lean_instInhabitedJson);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_OfScientific(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Hashable(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Data_TreeMap_Raw_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Substring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Json_Basic(builtin);
}
