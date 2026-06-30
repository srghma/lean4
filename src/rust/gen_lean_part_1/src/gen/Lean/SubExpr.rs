// Lean compiler output
// Module: Lean.SubExpr
// Imports: Lean.Meta.Basic Init.Data.Format.Macro
use crate::ffi::{
    lean_array_get, lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push,
    lean_array_size, lean_array_to_list, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mod, lean_nat_mul, lean_nat_pow, lean_nat_shiftr, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_append, lean_string_dec_eq, lean_string_push,
    lean_string_utf8_byte_size, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::Format::Macro::{
    initialize_Init_Data_Format_Macro, runtime_initialize_Init_Data_Format_Macro,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Ord::Basic::l_instOrdNat___lam__0___boxed;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_String_quote};
use crate::r#gen::Init::Data::String::Defs::l_String_intercalate;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{l_Array_push___boxed, l_Function_comp};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getObjValD, l_Lean_Json_getStr_x3f, l_Lean_Json_mkObj,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Json_getTag_x3f, l_Lean_Json_parseCtorFields, l_Lean_Name_fromJson_x3f,
};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed, l_Lean_Expr_const___override,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
pub static mut l_Lean_SubExpr_Pos_maxChildren: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_SubExpr_Pos_typeCoord: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_SubExpr_Pos_root: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_SubExpr_Pos_instInhabited: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_Pos_head___closed__0_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 0],
    };
static mut l_Lean_SubExpr_Pos_head___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_head___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_head___closed__1_value: leanh::LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 80, 111, 115, 46, 104, 101,
            97, 100, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_head___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_head___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_head___closed__2_value: leanh::LeanStringObject<15> =
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
            97, 108, 114, 101, 97, 100, 121, 32, 97, 116, 32, 116, 111, 112, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_head___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_head___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_Pos_head___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SubExpr_Pos_head___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_Pos_tail___closed__0_value: leanh::LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 80, 111, 115, 46, 116, 97,
            105, 108, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_tail___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_tail___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_Pos_tail___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SubExpr_Pos_tail___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_Pos_push___closed__0_value: leanh::LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 80, 111, 115, 46, 112, 117,
            115, 104, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_push___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_push___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_push___closed__1_value: leanh::LeanStringObject<20> =
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
            105, 110, 118, 97, 108, 105, 100, 32, 99, 111, 111, 114, 100, 105, 110, 97, 116, 101,
            32, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_push___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_push___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_depth___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_depth___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_depth___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_depth___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_append___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_push___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_append___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_append___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_toArray___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Array_push___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_SubExpr_Pos_toArray___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_toArray___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_toArray___closed__1_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_SubExpr_Pos_toArray___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_toArray___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_toString___closed__0_value: leanh::LeanStringObject<2> =
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
static mut l_Lean_SubExpr_Pos_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0_value:
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
    m_data: [48, 0],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1_value:
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
    m_data: [49, 0],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2_value:
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
    m_data: [50, 0],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3_value:
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
    m_data: [51, 0],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4_value:
    leanh::LeanStringObject<20> = leanh::LeanStringObject {
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
        73, 110, 118, 97, 108, 105, 100, 32, 99, 111, 111, 114, 100, 105, 110, 97, 116, 101, 32, 0,
    ],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((3 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((2 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
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
static mut l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8_value
) as *mut leanh::LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [44, 32, 0]};
static mut l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1_value:
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
    m_data: [91, 0],
};
static mut l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2_value:
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
static mut l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_fromString_x3f___closed__0_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [109, 97, 108, 102, 111, 114, 109, 101, 100, 32, 0],
    };
static mut l_Lean_SubExpr_Pos_fromString_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_fromString_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_fromString_x3f___closed__1_value: leanh::LeanArrayObject<0> =
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
static mut l_Lean_SubExpr_Pos_fromString_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_fromString_x3f___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_fromString_x3f___closed__2_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
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
static mut l_Lean_SubExpr_Pos_fromString_x3f___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_fromString_x3f___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_fromString_x21___closed__0_value: leanh::LeanStringObject<29> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 80, 111, 115, 46, 102, 114,
            111, 109, 83, 116, 114, 105, 110, 103, 33, 0,
        ],
    };
static mut l_Lean_SubExpr_Pos_fromString_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_fromString_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instOrd___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instOrdNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_instOrd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instOrd___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instOrd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instOrd___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instEmptyCollection: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value: leanh::LeanStringObject<
    17,
> = leanh::LeanStringObject {
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
        80, 111, 115, 46, 102, 114, 111, 109, 83, 116, 114, 105, 110, 103, 33, 32, 0,
    ],
};
static mut l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instRepr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_instRepr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instRepr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instToJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_instToJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_instToJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instToJson___closed__1_value: leanh::LeanClosureObject<5> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Function_comp as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 5,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToJson___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_SubExpr_Pos_instToJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instToJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instToJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_Pos_instFromJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_Pos_instFromJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_Pos_instFromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_Pos_instFromJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_Pos_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedSubExpr_default___closed__0_value: leanh::LeanStringObject<
    20,
> = leanh::LeanStringObject {
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
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_instInhabitedSubExpr_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedSubExpr_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedSubExpr_default___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_instInhabitedSubExpr_default___closed__0_value)
                as *mut leanh::LeanObject,
            17542774118954891045 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instInhabitedSubExpr_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedSubExpr_default___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instInhabitedSubExpr_default___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedSubExpr_default___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instInhabitedSubExpr_default___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instInhabitedSubExpr_default___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedSubExpr_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedSubExpr: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_bindingBody_x21___closed__0_value: leanh::LeanStringObject<26> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 98, 105, 110, 100, 105, 110,
            103, 66, 111, 100, 121, 33, 0,
        ],
    };
static mut l_Lean_SubExpr_bindingBody_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_bindingBody_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_bindingBody_x21___closed__1_value: leanh::LeanStringObject<24> =
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
            115, 117, 98, 101, 120, 112, 114, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 98, 105,
            110, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_SubExpr_bindingBody_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_bindingBody_x21___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_bindingBody_x21___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SubExpr_bindingBody_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_bindingDomain_x21___closed__0_value: leanh::LeanStringObject<28> =
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
            76, 101, 97, 110, 46, 83, 117, 98, 69, 120, 112, 114, 46, 98, 105, 110, 100, 105, 110,
            103, 68, 111, 109, 97, 105, 110, 33, 0,
        ],
    };
static mut l_Lean_SubExpr_bindingDomain_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_bindingDomain_x21___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_bindingDomain_x21___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_SubExpr_bindingDomain_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_SubExpr_instToJsonFVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_instToJsonFVarId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_instToJsonFVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instToJsonFVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instToJsonMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonFVarId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_SubExpr_instFromJsonFVarId___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_SubExpr_instFromJsonFVarId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instFromJsonFVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instFromJsonMVarId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonFVarId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 97, 103, 32, 102, 111,
        117, 110, 100, 0,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2_value:
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
    m_data: [116, 97, 114, 103, 101, 116, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3_value:
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
    m_data: [104, 121, 112, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4_value:
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
    m_data: [104, 121, 112, 84, 121, 112, 101, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [104, 121, 112, 86, 97, 108, 117, 101, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value:
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
        110, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 99, 111, 110, 115, 116, 114,
        117, 99, 116, 111, 114, 32, 109, 97, 116, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value:
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
    m_fun: l_Lean_SubExpr_instFromJsonGoalLocation_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SubExpr_instFromJsonGoalLocation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instFromJsonGoalLocation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value:
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
    m_fun: l_Lean_SubExpr_instToJsonGoalLocation_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SubExpr_instToJsonGoalLocation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instToJsonGoalLocation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonGoalLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value:
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
    m_data: [109, 118, 97, 114, 73, 100, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value:
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
    m_data: [83, 117, 98, 69, 120, 112, 114, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value:
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
        71, 111, 97, 108, 115, 76, 111, 99, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__2_value)
            as *mut leanh::LeanObject,
        15103157153926448042 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__3_value)
            as *mut leanh::LeanObject,
        5026744712064540828 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6_value:
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
    m_data: [46, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        6470623633356687478 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11_value:
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
    m_data: [58, 32, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value:
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
    m_data: [108, 111, 99, 0],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13_value)
            as *mut leanh::LeanObject,
        11768652256252909131 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value:
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
    m_fun: l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instFromJsonGoalsLocation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instFromJsonGoalsLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0_value:
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
static mut l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value:
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
    m_fun: l_Lean_SubExpr_instToJsonGoalsLocation_toJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_SubExpr_instToJsonGoalsLocation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_SubExpr_instToJsonGoalsLocation: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_SubExpr_instToJsonGoalsLocation___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_SubExpr_Pos_maxChildren() -> *mut leanh::LeanObject {
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1292_ = leanh::lean_unsigned_to_nat(4);
    return v___x_1292_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_typeCoord() -> *mut leanh::LeanObject {
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1293_ = leanh::lean_unsigned_to_nat(3);
    return v___x_1293_;
}
pub unsafe fn l_Lean_SubExpr_Pos_asNat(
    mut v_a_1294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_a_1294_);
    return v_a_1294_;
}
pub unsafe fn l_Lean_SubExpr_Pos_asNat___boxed(
    mut v_a_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_Lean_SubExpr_Pos_asNat(v_a_1295_);
    leanh::lean_dec(v_a_1295_);
    return v_res_1296_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_root() -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = leanh::lean_unsigned_to_nat(1);
    return v___x_1297_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_instInhabited() -> *mut leanh::LeanObject {
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = leanh::lean_unsigned_to_nat(1);
    return v___x_1298_;
}
pub unsafe fn l_Lean_SubExpr_Pos_isRoot(mut v_p_1299_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    v___x_1300_ = leanh::lean_unsigned_to_nat(4);
    v___x_1301_ = lean_nat_dec_lt(v_p_1299_, v___x_1300_);
    return v___x_1301_;
}
pub unsafe fn l_Lean_SubExpr_Pos_isRoot___boxed(
    mut v_p_1302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1303_: u8 = 0;
    let mut v_r_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1303_ = l_Lean_SubExpr_Pos_isRoot(v_p_1302_);
    leanh::lean_dec(v_p_1302_);
    v_r_1304_ = leanh::lean_box((v_res_1303_) as usize);
    return v_r_1304_;
}
pub unsafe fn l_panic___at___00Lean_SubExpr_Pos_head_spec__0(
    mut v_msg_1305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1306_ = leanh::lean_unsigned_to_nat(0);
    v___x_1307_ = lean_panic_fn_borrowed(v___x_1306_, v_msg_1305_);
    return v___x_1307_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_head___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1311_ = l_Lean_SubExpr_Pos_head___closed__2;
    v___x_1312_ = leanh::lean_unsigned_to_nat(19);
    v___x_1313_ = leanh::lean_unsigned_to_nat(46);
    v___x_1314_ = l_Lean_SubExpr_Pos_head___closed__1;
    v___x_1315_ = l_Lean_SubExpr_Pos_head___closed__0;
    v___x_1316_ = l_mkPanicMessageWithDecl(
        v___x_1315_,
        v___x_1314_,
        v___x_1313_,
        v___x_1312_,
        v___x_1311_,
    );
    return v___x_1316_;
}
pub unsafe fn l_Lean_SubExpr_Pos_head(
    mut v_p_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1318_: u8 = 0;
    v___x_1318_ = l_Lean_SubExpr_Pos_isRoot(v_p_1317_);
    if v___x_1318_ == 0 {
        let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1319_ = leanh::lean_unsigned_to_nat(4);
        v___x_1320_ = lean_nat_mod(v_p_1317_, v___x_1319_);
        return v___x_1320_;
    } else {
        let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1321_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SubExpr_Pos_head___closed__3),
            core::ptr::addr_of_mut!(l_Lean_SubExpr_Pos_head___closed__3_once),
            _init_l_Lean_SubExpr_Pos_head___closed__3,
        );
        v___x_1322_ = l_panic___at___00Lean_SubExpr_Pos_head_spec__0(v___x_1321_);
        return v___x_1322_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_head___boxed(
    mut v_p_1323_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1324_ = l_Lean_SubExpr_Pos_head(v_p_1323_);
    leanh::lean_dec(v_p_1323_);
    return v_res_1324_;
}
pub unsafe fn l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(
    mut v_msg_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1326_ = leanh::lean_unsigned_to_nat(1);
    v___x_1327_ = lean_panic_fn_borrowed(v___x_1326_, v_msg_1325_);
    return v___x_1327_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_tail___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1329_ = l_Lean_SubExpr_Pos_head___closed__2;
    v___x_1330_ = leanh::lean_unsigned_to_nat(19);
    v___x_1331_ = leanh::lean_unsigned_to_nat(50);
    v___x_1332_ = l_Lean_SubExpr_Pos_tail___closed__0;
    v___x_1333_ = l_Lean_SubExpr_Pos_head___closed__0;
    v___x_1334_ = l_mkPanicMessageWithDecl(
        v___x_1333_,
        v___x_1332_,
        v___x_1331_,
        v___x_1330_,
        v___x_1329_,
    );
    return v___x_1334_;
}
pub unsafe fn l_Lean_SubExpr_Pos_tail(
    mut v_p_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: u8 = 0;
    v___x_1336_ = l_Lean_SubExpr_Pos_isRoot(v_p_1335_);
    if v___x_1336_ == 0 {
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1337_ = l_Lean_SubExpr_Pos_head(v_p_1335_);
        v___x_1338_ = lean_nat_sub(v_p_1335_, v___x_1337_);
        leanh::lean_dec(v___x_1337_);
        v___x_1339_ = leanh::lean_unsigned_to_nat(2);
        v___x_1340_ = lean_nat_shiftr(v___x_1338_, v___x_1339_);
        leanh::lean_dec(v___x_1338_);
        return v___x_1340_;
    } else {
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1341_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_SubExpr_Pos_tail___closed__1),
            core::ptr::addr_of_mut!(l_Lean_SubExpr_Pos_tail___closed__1_once),
            _init_l_Lean_SubExpr_Pos_tail___closed__1,
        );
        v___x_1342_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_1341_);
        return v___x_1342_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_tail___boxed(
    mut v_p_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Lean_SubExpr_Pos_tail(v_p_1343_);
    leanh::lean_dec(v_p_1343_);
    return v_res_1344_;
}
pub unsafe fn l_Lean_SubExpr_Pos_push(
    mut v_p_1347_: *mut leanh::LeanObject,
    mut v_c_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: u8 = 0;
    v___x_1349_ = leanh::lean_unsigned_to_nat(4);
    v___x_1350_ = lean_nat_dec_le(v___x_1349_, v_c_1348_);
    if v___x_1350_ == 0 {
        let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1351_ = lean_nat_mul(v_p_1347_, v___x_1349_);
        v___x_1352_ = lean_nat_add(v___x_1351_, v_c_1348_);
        leanh::lean_dec(v_c_1348_);
        leanh::lean_dec(v___x_1351_);
        return v___x_1352_;
    } else {
        let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1353_ = l_Lean_SubExpr_Pos_head___closed__0;
        v___x_1354_ = l_Lean_SubExpr_Pos_push___closed__0;
        v___x_1355_ = leanh::lean_unsigned_to_nat(54);
        v___x_1356_ = leanh::lean_unsigned_to_nat(27);
        v___x_1357_ = l_Lean_SubExpr_Pos_push___closed__1;
        v___x_1358_ = l_Nat_reprFast(v_c_1348_);
        v___x_1359_ = lean_string_append(v___x_1357_, v___x_1358_);
        leanh::lean_dec_ref(v___x_1358_);
        v___x_1360_ = l_mkPanicMessageWithDecl(
            v___x_1353_,
            v___x_1354_,
            v___x_1355_,
            v___x_1356_,
            v___x_1359_,
        );
        leanh::lean_dec_ref(v___x_1359_);
        v___x_1361_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_1360_);
        return v___x_1361_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_push___boxed(
    mut v_p_1362_: *mut leanh::LeanObject,
    mut v_c_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_Lean_SubExpr_Pos_push(v_p_1362_, v_c_1363_);
    leanh::lean_dec(v_p_1362_);
    return v_res_1364_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldl___redArg(
    mut v_f_1365_: *mut leanh::LeanObject,
    mut v_init_1366_: *mut leanh::LeanObject,
    mut v_p_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1368_: u8 = 0;
    v___x_1368_ = l_Lean_SubExpr_Pos_isRoot(v_p_1367_);
    if v___x_1368_ == 0 {
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1369_ = l_Lean_SubExpr_Pos_tail(v_p_1367_);
        leanh::lean_inc(v_f_1365_);
        v___x_1370_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_1365_, v_init_1366_, v___x_1369_);
        leanh::lean_dec(v___x_1369_);
        v___x_1371_ = l_Lean_SubExpr_Pos_head(v_p_1367_);
        v___x_1372_ = leanh::lean_apply_2(v_f_1365_, v___x_1370_, v___x_1371_);
        return v___x_1372_;
    } else {
        leanh::lean_dec(v_f_1365_);
        leanh::lean_inc(v_init_1366_);
        return v_init_1366_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_foldl___redArg___boxed(
    mut v_f_1373_: *mut leanh::LeanObject,
    mut v_init_1374_: *mut leanh::LeanObject,
    mut v_p_1375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1376_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_1373_, v_init_1374_, v_p_1375_);
    leanh::lean_dec(v_p_1375_);
    leanh::lean_dec(v_init_1374_);
    return v_res_1376_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldl(
    mut v_00_u03b1_1377_: *mut leanh::LeanObject,
    mut v_f_1378_: *mut leanh::LeanObject,
    mut v_init_1379_: *mut leanh::LeanObject,
    mut v_p_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = l_Lean_SubExpr_Pos_foldl___redArg(v_f_1378_, v_init_1379_, v_p_1380_);
    return v___x_1381_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldl___boxed(
    mut v_00_u03b1_1382_: *mut leanh::LeanObject,
    mut v_f_1383_: *mut leanh::LeanObject,
    mut v_init_1384_: *mut leanh::LeanObject,
    mut v_p_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1386_ = l_Lean_SubExpr_Pos_foldl(v_00_u03b1_1382_, v_f_1383_, v_init_1384_, v_p_1385_);
    leanh::lean_dec(v_p_1385_);
    leanh::lean_dec(v_init_1384_);
    return v_res_1386_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldr___redArg(
    mut v_f_1387_: *mut leanh::LeanObject,
    mut v_p_1388_: *mut leanh::LeanObject,
    mut v_init_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1390_: u8 = 0;
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1390_ = l_Lean_SubExpr_Pos_isRoot(v_p_1388_);
                if v___x_1390_ == 0 {
                    v___x_1391_ = l_Lean_SubExpr_Pos_tail(v_p_1388_);
                    v___x_1392_ = l_Lean_SubExpr_Pos_head(v_p_1388_);
                    leanh::lean_dec(v_p_1388_);
                    leanh::lean_inc(v_f_1387_);
                    v___x_1393_ = leanh::lean_apply_2(v_f_1387_, v___x_1392_, v_init_1389_);
                    v_p_1388_ = v___x_1391_;
                    v_init_1389_ = v___x_1393_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_p_1388_);
                    leanh::lean_dec(v_f_1387_);
                    return v_init_1389_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_foldr(
    mut v_00_u03b1_1395_: *mut leanh::LeanObject,
    mut v_f_1396_: *mut leanh::LeanObject,
    mut v_p_1397_: *mut leanh::LeanObject,
    mut v_init_1398_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1399_ = l_Lean_SubExpr_Pos_foldr___redArg(v_f_1396_, v_p_1397_, v_init_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(
    mut v_p_1400_: *mut leanh::LeanObject,
    mut v_f_1401_: *mut leanh::LeanObject,
    mut v_x_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = l_Lean_SubExpr_Pos_head(v_p_1400_);
    v___x_1404_ = leanh::lean_apply_2(v_f_1401_, v_x_1402_, v___x_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed(
    mut v_p_1405_: *mut leanh::LeanObject,
    mut v_f_1406_: *mut leanh::LeanObject,
    mut v_x_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1408_ = l_Lean_SubExpr_Pos_foldlM___redArg___lam__0(v_p_1405_, v_f_1406_, v_x_1407_);
    leanh::lean_dec(v_p_1405_);
    return v_res_1408_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldlM___redArg(
    mut v_inst_1409_: *mut leanh::LeanObject,
    mut v_f_1410_: *mut leanh::LeanObject,
    mut v_init_1411_: *mut leanh::LeanObject,
    mut v_p_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: u8 = 0;
    v___x_1413_ = l_Lean_SubExpr_Pos_isRoot(v_p_1412_);
    if v___x_1413_ == 0 {
        let mut v_toBind_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1414_ = leanh::lean_ctor_get(v_inst_1409_, 1);
        leanh::lean_inc(v_toBind_1414_);
        leanh::lean_inc(v_f_1410_);
        leanh::lean_inc(v_p_1412_);
        v___f_1415_ = leanh::lean_alloc_closure(
            l_Lean_SubExpr_Pos_foldlM___redArg___lam__0___boxed as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_1415_, 0, v_p_1412_);
        leanh::lean_closure_set(v___f_1415_, 1, v_f_1410_);
        v___x_1416_ = l_Lean_SubExpr_Pos_tail(v_p_1412_);
        leanh::lean_dec(v_p_1412_);
        v___x_1417_ =
            l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1409_, v_f_1410_, v_init_1411_, v___x_1416_);
        v___x_1418_ = leanh::lean_apply_4(
            v_toBind_1414_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1417_,
            v___f_1415_,
        );
        return v___x_1418_;
    } else {
        let mut v_toApplicative_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_1412_);
        leanh::lean_dec(v_f_1410_);
        v_toApplicative_1419_ = leanh::lean_ctor_get(v_inst_1409_, 0);
        leanh::lean_inc_ref(v_toApplicative_1419_);
        leanh::lean_dec_ref(v_inst_1409_);
        v_toPure_1420_ = leanh::lean_ctor_get(v_toApplicative_1419_, 1);
        leanh::lean_inc(v_toPure_1420_);
        leanh::lean_dec_ref(v_toApplicative_1419_);
        v___x_1421_ =
            leanh::lean_apply_2(v_toPure_1420_, leanh::lean_box(0), v_init_1411_);
        return v___x_1421_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_foldlM(
    mut v_00_u03b1_1422_: *mut leanh::LeanObject,
    mut v_inst_1423_: *mut leanh::LeanObject,
    mut v_M_1424_: *mut leanh::LeanObject,
    mut v_inst_1425_: *mut leanh::LeanObject,
    mut v_f_1426_: *mut leanh::LeanObject,
    mut v_init_1427_: *mut leanh::LeanObject,
    mut v_p_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1429_ =
        l_Lean_SubExpr_Pos_foldlM___redArg(v_inst_1425_, v_f_1426_, v_init_1427_, v_p_1428_);
    return v___x_1429_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldlM___boxed(
    mut v_00_u03b1_1430_: *mut leanh::LeanObject,
    mut v_inst_1431_: *mut leanh::LeanObject,
    mut v_M_1432_: *mut leanh::LeanObject,
    mut v_inst_1433_: *mut leanh::LeanObject,
    mut v_f_1434_: *mut leanh::LeanObject,
    mut v_init_1435_: *mut leanh::LeanObject,
    mut v_p_1436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1437_ = l_Lean_SubExpr_Pos_foldlM(
        v_00_u03b1_1430_,
        v_inst_1431_,
        v_M_1432_,
        v_inst_1433_,
        v_f_1434_,
        v_init_1435_,
        v_p_1436_,
    );
    leanh::lean_dec(v_inst_1431_);
    return v_res_1437_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM___redArg___boxed(
    mut v_inst_1438_: *mut leanh::LeanObject,
    mut v_f_1439_: *mut leanh::LeanObject,
    mut v_p_1440_: *mut leanh::LeanObject,
    mut v_init_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1442_ =
        l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_1438_, v_f_1439_, v_p_1440_, v_init_1441_);
    leanh::lean_dec(v_p_1440_);
    return v_res_1442_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM___redArg(
    mut v_inst_1443_: *mut leanh::LeanObject,
    mut v_f_1444_: *mut leanh::LeanObject,
    mut v_p_1445_: *mut leanh::LeanObject,
    mut v_init_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1447_: u8 = 0;
    v___x_1447_ = l_Lean_SubExpr_Pos_isRoot(v_p_1445_);
    if v___x_1447_ == 0 {
        let mut v_toBind_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1448_ = leanh::lean_ctor_get(v_inst_1443_, 1);
        leanh::lean_inc(v_toBind_1448_);
        v___x_1449_ = l_Lean_SubExpr_Pos_head(v_p_1445_);
        leanh::lean_inc(v_f_1444_);
        v___x_1450_ = leanh::lean_apply_2(v_f_1444_, v___x_1449_, v_init_1446_);
        v___x_1451_ = l_Lean_SubExpr_Pos_tail(v_p_1445_);
        v___x_1452_ = leanh::lean_alloc_closure(
            l_Lean_SubExpr_Pos_foldrM___redArg___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___x_1452_, 0, v_inst_1443_);
        leanh::lean_closure_set(v___x_1452_, 1, v_f_1444_);
        leanh::lean_closure_set(v___x_1452_, 2, v___x_1451_);
        v___x_1453_ = leanh::lean_apply_4(
            v_toBind_1448_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1450_,
            v___x_1452_,
        );
        return v___x_1453_;
    } else {
        let mut v_toApplicative_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_f_1444_);
        v_toApplicative_1454_ = leanh::lean_ctor_get(v_inst_1443_, 0);
        leanh::lean_inc_ref(v_toApplicative_1454_);
        leanh::lean_dec_ref(v_inst_1443_);
        v_toPure_1455_ = leanh::lean_ctor_get(v_toApplicative_1454_, 1);
        leanh::lean_inc(v_toPure_1455_);
        leanh::lean_dec_ref(v_toApplicative_1454_);
        v___x_1456_ =
            leanh::lean_apply_2(v_toPure_1455_, leanh::lean_box(0), v_init_1446_);
        return v___x_1456_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM(
    mut v_00_u03b1_1457_: *mut leanh::LeanObject,
    mut v_M_1458_: *mut leanh::LeanObject,
    mut v_inst_1459_: *mut leanh::LeanObject,
    mut v_f_1460_: *mut leanh::LeanObject,
    mut v_p_1461_: *mut leanh::LeanObject,
    mut v_init_1462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1463_ =
        l_Lean_SubExpr_Pos_foldrM___redArg(v_inst_1459_, v_f_1460_, v_p_1461_, v_init_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM___boxed(
    mut v_00_u03b1_1464_: *mut leanh::LeanObject,
    mut v_M_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
    mut v_f_1467_: *mut leanh::LeanObject,
    mut v_p_1468_: *mut leanh::LeanObject,
    mut v_init_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_SubExpr_Pos_foldrM(
        v_00_u03b1_1464_,
        v_M_1465_,
        v_inst_1466_,
        v_f_1467_,
        v_p_1468_,
        v_init_1469_,
    );
    leanh::lean_dec(v_p_1468_);
    return v_res_1470_;
}
pub unsafe fn l_Lean_SubExpr_Pos_depth___lam__0(
    mut v_x_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1473_ = leanh::lean_unsigned_to_nat(1);
    v___x_1474_ = lean_nat_add(v___y_1472_, v___x_1473_);
    return v___x_1474_;
}
pub unsafe fn l_Lean_SubExpr_Pos_depth___lam__0___boxed(
    mut v_x_1475_: *mut leanh::LeanObject,
    mut v___y_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ = l_Lean_SubExpr_Pos_depth___lam__0(v_x_1475_, v___y_1476_);
    leanh::lean_dec(v___y_1476_);
    leanh::lean_dec(v_x_1475_);
    return v_res_1477_;
}
pub unsafe fn l_Lean_SubExpr_Pos_depth(
    mut v_p_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1480_ = l_Lean_SubExpr_Pos_depth___closed__0;
    v___x_1481_ = leanh::lean_unsigned_to_nat(0);
    v___x_1482_ = l_Lean_SubExpr_Pos_foldr___redArg(v___f_1480_, v_p_1479_, v___x_1481_);
    return v___x_1482_;
}
pub unsafe fn l_Lean_SubExpr_Pos_all___lam__0(
    mut v_pred_1483_: *mut leanh::LeanObject,
    mut v_n_1484_: *mut leanh::LeanObject,
    mut v_a_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    v___x_1486_ = leanh::lean_apply_1(v_pred_1483_, v_n_1484_);
    v___x_1487_ = (leanh::lean_unbox(v___x_1486_) as u8);
    if v___x_1487_ == 0 {
        let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1488_ = leanh::lean_box(0);
        return v___x_1488_;
    } else {
        let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1489_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1489_, 0, v_a_1485_);
        return v___x_1489_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(
    mut v_f_1490_: *mut leanh::LeanObject,
    mut v_p_1491_: *mut leanh::LeanObject,
    mut v_init_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1493_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1493_ = l_Lean_SubExpr_Pos_isRoot(v_p_1491_);
                if v___x_1493_ == 0 {
                    v___x_1494_ = l_Lean_SubExpr_Pos_head(v_p_1491_);
                    leanh::lean_inc_ref(v_f_1490_);
                    v___x_1495_ = leanh::lean_apply_2(v_f_1490_, v___x_1494_, v_init_1492_);
                    if leanh::lean_obj_tag(v___x_1495_) == 0 {
                        leanh::lean_dec(v_p_1491_);
                        leanh::lean_dec_ref(v_f_1490_);
                        return v___x_1495_;
                    } else {
                        v_val_1496_ = leanh::lean_ctor_get(v___x_1495_, 0);
                        leanh::lean_inc(v_val_1496_);
                        leanh::lean_dec_ref_known(v___x_1495_, 1);
                        v___x_1497_ = l_Lean_SubExpr_Pos_tail(v_p_1491_);
                        leanh::lean_dec(v_p_1491_);
                        v_p_1491_ = v___x_1497_;
                        v_init_1492_ = v_val_1496_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_1491_);
                    leanh::lean_dec_ref(v_f_1490_);
                    v___x_1499_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1499_, 0, v_init_1492_);
                    return v___x_1499_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_all(
    mut v_pred_1500_: *mut leanh::LeanObject,
    mut v_p_1501_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___f_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1502_ = leanh::lean_alloc_closure(
        l_Lean_SubExpr_Pos_all___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1502_, 0, v_pred_1500_);
    v___x_1503_ = leanh::lean_box(0);
    v___x_1504_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(
        v___f_1502_,
        v_p_1501_,
        v___x_1503_,
    );
    if leanh::lean_obj_tag(v___x_1504_) == 0 {
        let mut v___x_1505_: u8 = 0;
        v___x_1505_ = 0;
        return v___x_1505_;
    } else {
        let mut v___x_1506_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_1504_, 1);
        v___x_1506_ = 1;
        return v___x_1506_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_all___boxed(
    mut v_pred_1507_: *mut leanh::LeanObject,
    mut v_p_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1509_: u8 = 0;
    let mut v_r_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1509_ = l_Lean_SubExpr_Pos_all(v_pred_1507_, v_p_1508_);
    v_r_1510_ = leanh::lean_box((v_res_1509_) as usize);
    return v_r_1510_;
}
pub unsafe fn l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0(
    mut v_00_u03b1_1511_: *mut leanh::LeanObject,
    mut v_f_1512_: *mut leanh::LeanObject,
    mut v_p_1513_: *mut leanh::LeanObject,
    mut v_init_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = l_Lean_SubExpr_Pos_foldrM___at___00Lean_SubExpr_Pos_all_spec__0___redArg(
        v_f_1512_,
        v_p_1513_,
        v_init_1514_,
    );
    return v___x_1515_;
}
pub unsafe fn l_Lean_SubExpr_Pos_append(
    mut v_init_1517_: *mut leanh::LeanObject,
    mut v_p_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lean_SubExpr_Pos_append___closed__0;
    v___x_1520_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_1519_, v_init_1517_, v_p_1518_);
    return v___x_1520_;
}
pub unsafe fn l_Lean_SubExpr_Pos_append___boxed(
    mut v_init_1521_: *mut leanh::LeanObject,
    mut v_p_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l_Lean_SubExpr_Pos_append(v_init_1521_, v_p_1522_);
    leanh::lean_dec(v_p_1522_);
    leanh::lean_dec(v_init_1521_);
    return v_res_1523_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(
    mut v_as_1524_: *mut leanh::LeanObject,
    mut v_i_1525_: usize,
    mut v_stop_1526_: usize,
    mut v_b_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: usize = 0;
    let mut v___x_1532_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1528_ = lean_usize_dec_eq(v_i_1525_, v_stop_1526_);
                if v___x_1528_ == 0 {
                    v___x_1529_ = lean_array_uget_borrowed(v_as_1524_, v_i_1525_);
                    leanh::lean_inc(v___x_1529_);
                    v___x_1530_ = l_Lean_SubExpr_Pos_push(v_b_1527_, v___x_1529_);
                    leanh::lean_dec(v_b_1527_);
                    v___x_1531_ = 1usize;
                    v___x_1532_ = lean_usize_add(v_i_1525_, v___x_1531_);
                    v_i_1525_ = v___x_1532_;
                    v_b_1527_ = v___x_1530_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1527_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0___boxed(
    mut v_as_1534_: *mut leanh::LeanObject,
    mut v_i_1535_: *mut leanh::LeanObject,
    mut v_stop_1536_: *mut leanh::LeanObject,
    mut v_b_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1538_: usize = 0;
    let mut v_stop_boxed_1539_: usize = 0;
    let mut v_res_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1538_ = leanh::lean_unbox_usize(v_i_1535_);
    leanh::lean_dec(v_i_1535_);
    v_stop_boxed_1539_ = leanh::lean_unbox_usize(v_stop_1536_);
    leanh::lean_dec(v_stop_1536_);
    v_res_1540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_as_1534_, v_i_boxed_1538_, v_stop_boxed_1539_, v_b_1537_);
    leanh::lean_dec_ref(v_as_1534_);
    return v_res_1540_;
}
pub unsafe fn l_Lean_SubExpr_Pos_ofArray(
    mut v_ps_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    v___x_1542_ = leanh::lean_unsigned_to_nat(1);
    v___x_1543_ = leanh::lean_unsigned_to_nat(0);
    v___x_1544_ = lean_array_get_size(v_ps_1541_);
    v___x_1545_ = lean_nat_dec_lt(v___x_1543_, v___x_1544_);
    if v___x_1545_ == 0 {
        return v___x_1542_;
    } else {
        let mut v___x_1546_: u8 = 0;
        v___x_1546_ = lean_nat_dec_le(v___x_1544_, v___x_1544_);
        if v___x_1546_ == 0 {
            if v___x_1545_ == 0 {
                return v___x_1542_;
            } else {
                let mut v___x_1547_: usize = 0;
                let mut v___x_1548_: usize = 0;
                let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1547_ = 0usize;
                v___x_1548_ = lean_usize_of_nat(v___x_1544_);
                v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_1541_, v___x_1547_, v___x_1548_, v___x_1542_);
                return v___x_1549_;
            }
        } else {
            let mut v___x_1550_: usize = 0;
            let mut v___x_1551_: usize = 0;
            let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1550_ = 0usize;
            v___x_1551_ = lean_usize_of_nat(v___x_1544_);
            v___x_1552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_SubExpr_Pos_ofArray_spec__0(v_ps_1541_, v___x_1550_, v___x_1551_, v___x_1542_);
            return v___x_1552_;
        }
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_ofArray___boxed(
    mut v_ps_1553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1554_ = l_Lean_SubExpr_Pos_ofArray(v_ps_1553_);
    leanh::lean_dec_ref(v_ps_1553_);
    return v_res_1554_;
}
pub unsafe fn l_Lean_SubExpr_Pos_toArray(
    mut v_p_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = l_Lean_SubExpr_Pos_toArray___closed__0;
    v___x_1560_ = l_Lean_SubExpr_Pos_toArray___closed__1;
    v___x_1561_ = l_Lean_SubExpr_Pos_foldl___redArg(v___x_1559_, v___x_1560_, v_p_1558_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_SubExpr_Pos_toArray___boxed(
    mut v_p_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_SubExpr_Pos_toArray(v_p_1562_);
    leanh::lean_dec(v_p_1562_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushBindingDomain(
    mut v_p_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1565_ = leanh::lean_unsigned_to_nat(0);
    v___x_1566_ = l_Lean_SubExpr_Pos_push(v_p_1564_, v___x_1565_);
    return v___x_1566_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushBindingDomain___boxed(
    mut v_p_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_p_1567_);
    leanh::lean_dec(v_p_1567_);
    return v_res_1568_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushBindingBody(
    mut v_p_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = leanh::lean_unsigned_to_nat(1);
    v___x_1571_ = l_Lean_SubExpr_Pos_push(v_p_1569_, v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushBindingBody___boxed(
    mut v_p_1572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ = l_Lean_SubExpr_Pos_pushBindingBody(v_p_1572_);
    leanh::lean_dec(v_p_1572_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetVarType(
    mut v_p_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = leanh::lean_unsigned_to_nat(0);
    v___x_1576_ = l_Lean_SubExpr_Pos_push(v_p_1574_, v___x_1575_);
    return v___x_1576_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetVarType___boxed(
    mut v_p_1577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1578_ = l_Lean_SubExpr_Pos_pushLetVarType(v_p_1577_);
    leanh::lean_dec(v_p_1577_);
    return v_res_1578_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetValue(
    mut v_p_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = leanh::lean_unsigned_to_nat(1);
    v___x_1581_ = l_Lean_SubExpr_Pos_push(v_p_1579_, v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetValue___boxed(
    mut v_p_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1583_ = l_Lean_SubExpr_Pos_pushLetValue(v_p_1582_);
    leanh::lean_dec(v_p_1582_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetBody(
    mut v_p_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1585_ = leanh::lean_unsigned_to_nat(2);
    v___x_1586_ = l_Lean_SubExpr_Pos_push(v_p_1584_, v___x_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushLetBody___boxed(
    mut v_p_1587_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Lean_SubExpr_Pos_pushLetBody(v_p_1587_);
    leanh::lean_dec(v_p_1587_);
    return v_res_1588_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushAppFn(
    mut v_p_1589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1590_ = leanh::lean_unsigned_to_nat(0);
    v___x_1591_ = l_Lean_SubExpr_Pos_push(v_p_1589_, v___x_1590_);
    return v___x_1591_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushAppFn___boxed(
    mut v_p_1592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1593_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_1592_);
    leanh::lean_dec(v_p_1592_);
    return v_res_1593_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushAppArg(
    mut v_p_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = leanh::lean_unsigned_to_nat(1);
    v___x_1596_ = l_Lean_SubExpr_Pos_push(v_p_1594_, v___x_1595_);
    return v___x_1596_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushAppArg___boxed(
    mut v_p_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_1597_);
    leanh::lean_dec(v_p_1597_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushProj(
    mut v_p_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = leanh::lean_unsigned_to_nat(0);
    v___x_1601_ = l_Lean_SubExpr_Pos_push(v_p_1599_, v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushProj___boxed(
    mut v_p_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_SubExpr_Pos_pushProj(v_p_1602_);
    leanh::lean_dec(v_p_1602_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushType(
    mut v_p_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = leanh::lean_unsigned_to_nat(3);
    v___x_1606_ = l_Lean_SubExpr_Pos_push(v_p_1604_, v___x_1605_);
    return v___x_1606_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushType___boxed(
    mut v_p_1607_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_Lean_SubExpr_Pos_pushType(v_p_1607_);
    leanh::lean_dec(v_p_1607_);
    return v_res_1608_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNaryFn(
    mut v_numArgs_1609_: *mut leanh::LeanObject,
    mut v_p_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = leanh::lean_unsigned_to_nat(4);
    v___x_1612_ = lean_nat_pow(v___x_1611_, v_numArgs_1609_);
    v___x_1613_ = lean_nat_mul(v_p_1610_, v___x_1612_);
    leanh::lean_dec(v___x_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNaryFn___boxed(
    mut v_numArgs_1614_: *mut leanh::LeanObject,
    mut v_p_1615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_Lean_SubExpr_Pos_pushNaryFn(v_numArgs_1614_, v_p_1615_);
    leanh::lean_dec(v_p_1615_);
    leanh::lean_dec(v_numArgs_1614_);
    return v_res_1616_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNaryArg(
    mut v_numArgs_1617_: *mut leanh::LeanObject,
    mut v_argIdx_1618_: *mut leanh::LeanObject,
    mut v_p_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = leanh::lean_unsigned_to_nat(4);
    v___x_1621_ = lean_nat_sub(v_numArgs_1617_, v_argIdx_1618_);
    v___x_1622_ = lean_nat_pow(v___x_1620_, v___x_1621_);
    leanh::lean_dec(v___x_1621_);
    v___x_1623_ = lean_nat_mul(v_p_1619_, v___x_1622_);
    leanh::lean_dec(v___x_1622_);
    v___x_1624_ = leanh::lean_unsigned_to_nat(1);
    v_this_1625_ = lean_nat_add(v___x_1623_, v___x_1624_);
    leanh::lean_dec(v___x_1623_);
    return v_this_1625_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNaryArg___boxed(
    mut v_numArgs_1626_: *mut leanh::LeanObject,
    mut v_argIdx_1627_: *mut leanh::LeanObject,
    mut v_p_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_SubExpr_Pos_pushNaryArg(v_numArgs_1626_, v_argIdx_1627_, v_p_1628_);
    leanh::lean_dec(v_p_1628_);
    leanh::lean_dec(v_argIdx_1627_);
    leanh::lean_dec(v_numArgs_1626_);
    return v_res_1629_;
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNthBindingDomain(
    mut v_x_1630_: *mut leanh::LeanObject,
    mut v_x_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1633_: u8 = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1632_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1633_ = lean_nat_dec_eq(v_x_1630_, v_zero_1632_);
                if v_isZero_1633_ == 1 {
                    leanh::lean_dec(v_x_1630_);
                    v___x_1634_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_x_1631_);
                    leanh::lean_dec(v_x_1631_);
                    return v___x_1634_;
                } else {
                    v_one_1635_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1636_ = lean_nat_sub(v_x_1630_, v_one_1635_);
                    leanh::lean_dec(v_x_1630_);
                    v___x_1637_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_1631_);
                    leanh::lean_dec(v_x_1631_);
                    v_x_1630_ = v_n_1636_;
                    v_x_1631_ = v___x_1637_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_pushNthBindingBody(
    mut v_x_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1642_: u8 = 0;
    let mut v_one_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1641_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1642_ = lean_nat_dec_eq(v_x_1639_, v_zero_1641_);
                if v_isZero_1642_ == 1 {
                    leanh::lean_dec(v_x_1639_);
                    return v_x_1640_;
                } else {
                    v_one_1643_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1644_ = lean_nat_sub(v_x_1639_, v_one_1643_);
                    leanh::lean_dec(v_x_1639_);
                    v___x_1645_ = l_Lean_SubExpr_Pos_pushBindingBody(v_x_1640_);
                    leanh::lean_dec(v_x_1640_);
                    v_x_1639_ = v_n_1644_;
                    v_x_1640_ = v___x_1645_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(
    mut v_a_1647_: *mut leanh::LeanObject,
    mut v_a_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1647_) == 0 {
                    v___x_1649_ = l_List_reverse___redArg(v_a_1648_);
                    return v___x_1649_;
                } else {
                    v_head_1650_ = leanh::lean_ctor_get(v_a_1647_, 0);
                    v_tail_1651_ = leanh::lean_ctor_get(v_a_1647_, 1);
                    v_isSharedCheck_1660_ = (!leanh::lean_is_exclusive(v_a_1647_)) as u8;
                    if v_isSharedCheck_1660_ == 0 {
                        v___x_1653_ = v_a_1647_;
                        v_isShared_1654_ = v_isSharedCheck_1660_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1651_);
                        leanh::lean_inc(v_head_1650_);
                        leanh::lean_dec(v_a_1647_);
                        v___x_1653_ = leanh::lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1660_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1655_ = l_Nat_reprFast(v_head_1650_);
                if v_isShared_1654_ == 0 {
                    leanh::lean_ctor_set(v___x_1653_, 1, v_a_1648_);
                    leanh::lean_ctor_set(v___x_1653_, 0, v___x_1655_);
                    v___x_1657_ = v___x_1653_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 1, v_a_1648_);
                    v___x_1657_ = v_reuseFailAlloc_1659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1647_ = v_tail_1651_;
                v_a_1648_ = v___x_1657_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_toString(
    mut v_p_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1663_ = l_Lean_SubExpr_Pos_toString___closed__0;
    v___x_1664_ = l_Lean_SubExpr_Pos_toArray(v_p_1662_);
    v___x_1665_ = lean_array_to_list(v___x_1664_);
    v___x_1666_ = leanh::lean_box(0);
    v___x_1667_ =
        l_List_mapTR_loop___at___00Lean_SubExpr_Pos_toString_spec__0(v___x_1665_, v___x_1666_);
    v___x_1668_ = l_String_intercalate(v___x_1663_, v___x_1667_);
    v___x_1669_ = lean_string_append(v___x_1663_, v___x_1668_);
    leanh::lean_dec_ref(v___x_1668_);
    return v___x_1669_;
}
pub unsafe fn l_Lean_SubExpr_Pos_toString___boxed(
    mut v_p_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_Lean_SubExpr_Pos_toString(v_p_1670_);
    leanh::lean_dec(v_p_1670_);
    return v_res_1671_;
}
pub unsafe fn l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(
    mut v_x_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: u8 = 0;
    v___x_1686_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__0;
    v___x_1687_ = lean_string_dec_eq(v_x_1685_, v___x_1686_);
    if v___x_1687_ == 0 {
        let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1689_: u8 = 0;
        v___x_1688_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__1;
        v___x_1689_ = lean_string_dec_eq(v_x_1685_, v___x_1688_);
        if v___x_1689_ == 0 {
            let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1691_: u8 = 0;
            v___x_1690_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__2;
            v___x_1691_ = lean_string_dec_eq(v_x_1685_, v___x_1690_);
            if v___x_1691_ == 0 {
                let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1693_: u8 = 0;
                v___x_1692_ =
                    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__3;
                v___x_1693_ = lean_string_dec_eq(v_x_1685_, v___x_1692_);
                if v___x_1693_ == 0 {
                    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1694_ =
                        l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__4;
                    v___x_1695_ = lean_string_append(v___x_1694_, v_x_1685_);
                    v___x_1696_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1696_, 0, v___x_1695_);
                    return v___x_1696_;
                } else {
                    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_1697_ =
                        l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__5;
                    return v___x_1697_;
                }
            } else {
                let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1698_ =
                    l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__6;
                return v___x_1698_;
            }
        } else {
            let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1699_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
            return v___x_1699_;
        }
    } else {
        let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1700_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__8;
        return v___x_1700_;
    }
}
pub unsafe fn l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___boxed(
    mut v_x_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_x_1701_);
    leanh::lean_dec_ref(v_x_1701_);
    return v_res_1702_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(
    mut v_s_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ =
        l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___closed__0;
    return v___x_1706_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1___boxed(
    mut v_s_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1708_ =
        l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v_s_1707_);
    leanh::lean_dec_ref(v_s_1707_);
    return v_res_1708_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(
    mut v_sz_1709_: usize,
    mut v_i_1710_: usize,
    mut v_bs_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: usize = 0;
    let mut v___x_1728_: usize = 0;
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1712_ = lean_usize_dec_lt(v_i_1710_, v_sz_1709_);
                if v___x_1712_ == 0 {
                    v___x_1713_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1713_, 0, v_bs_1711_);
                    return v___x_1713_;
                } else {
                    v_v_1714_ = lean_array_uget_borrowed(v_bs_1711_, v_i_1710_);
                    v___x_1715_ =
                        l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord(v_v_1714_);
                    if leanh::lean_obj_tag(v___x_1715_) == 0 {
                        leanh::lean_dec_ref(v_bs_1711_);
                        v_a_1716_ = leanh::lean_ctor_get(v___x_1715_, 0);
                        v_isSharedCheck_1723_ =
                            (!leanh::lean_is_exclusive(v___x_1715_)) as u8;
                        if v_isSharedCheck_1723_ == 0 {
                            v___x_1718_ = v___x_1715_;
                            v_isShared_1719_ = v_isSharedCheck_1723_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1716_);
                            leanh::lean_dec(v___x_1715_);
                            v___x_1718_ = leanh::lean_box(0);
                            v_isShared_1719_ = v_isSharedCheck_1723_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1724_ = leanh::lean_ctor_get(v___x_1715_, 0);
                        leanh::lean_inc(v_a_1724_);
                        leanh::lean_dec_ref_known(v___x_1715_, 1);
                        v___x_1725_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1726_ = lean_array_uset(v_bs_1711_, v_i_1710_, v___x_1725_);
                        v___x_1727_ = 1usize;
                        v___x_1728_ = lean_usize_add(v_i_1710_, v___x_1727_);
                        v___x_1729_ = lean_array_uset(v_bs_x27_1726_, v_i_1710_, v_a_1724_);
                        v_i_1710_ = v___x_1728_;
                        v_bs_1711_ = v___x_1729_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1719_ == 0 {
                    v___x_1721_ = v___x_1718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3___boxed(
    mut v_sz_1731_: *mut leanh::LeanObject,
    mut v_i_1732_: *mut leanh::LeanObject,
    mut v_bs_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1734_: usize = 0;
    let mut v_i_boxed_1735_: usize = 0;
    let mut v_res_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1734_ = leanh::lean_unbox_usize(v_sz_1731_);
    leanh::lean_dec(v_sz_1731_);
    v_i_boxed_1735_ = leanh::lean_unbox_usize(v_i_1732_);
    leanh::lean_dec(v_i_1732_);
    v_res_1736_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_boxed_1734_, v_i_boxed_1735_, v_bs_1733_);
    return v_res_1736_;
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(
    mut v_x_1738_: *mut leanh::LeanObject,
    mut v_x_1739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1739_) == 0 {
                    return v_x_1738_;
                } else {
                    v_head_1740_ = leanh::lean_ctor_get(v_x_1739_, 0);
                    v_tail_1741_ = leanh::lean_ctor_get(v_x_1739_, 1);
                    v___x_1742_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___closed__0;
                    v___x_1743_ = lean_string_append(v_x_1738_, v___x_1742_);
                    v___x_1744_ = lean_string_append(v___x_1743_, v_head_1740_);
                    v_x_1738_ = v___x_1744_;
                    v_x_1739_ = v_tail_1741_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0___boxed(
    mut v_x_1746_: *mut leanh::LeanObject,
    mut v_x_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v_x_1746_, v_x_1747_);
    leanh::lean_dec(v_x_1747_);
    return v_res_1748_;
}
pub unsafe fn l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(
    mut v_x_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1752_) == 0 {
        let mut v___x_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1753_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__0;
        return v___x_1753_;
    } else {
        let mut v_tail_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1754_ = leanh::lean_ctor_get(v_x_1752_, 1);
        if leanh::lean_obj_tag(v_tail_1754_) == 0 {
            let mut v_head_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1755_ = leanh::lean_ctor_get(v_x_1752_, 0);
            v___x_1756_ =
                l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1;
            v___x_1757_ = lean_string_append(v___x_1756_, v_head_1755_);
            v___x_1758_ =
                l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__2;
            v___x_1759_ = lean_string_append(v___x_1757_, v___x_1758_);
            return v___x_1759_;
        } else {
            let mut v_head_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1764_: u32 = 0;
            let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_1760_ = leanh::lean_ctor_get(v_x_1752_, 0);
            v___x_1761_ =
                l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___closed__1;
            v___x_1762_ = lean_string_append(v___x_1761_, v_head_1760_);
            v___x_1763_ = l_List_foldl___at___00List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0_spec__0(v___x_1762_, v_tail_1754_);
            v___x_1764_ = 93;
            v___x_1765_ = lean_string_push(v___x_1763_, v___x_1764_);
            return v___x_1765_;
        }
    }
}
pub unsafe fn l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0___boxed(
    mut v_x_1766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1767_ = l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_x_1766_);
    leanh::lean_dec(v_x_1766_);
    return v_res_1767_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(
    mut v_x_1768_: *mut leanh::LeanObject,
    mut v___x_1769_: *mut leanh::LeanObject,
    mut v___x_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_b_1772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_it_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currPos_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1785_: u8 = 0;
    let mut v_startInclusive_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: u8 = 0;
    let mut v___x_1790_: u32 = 0;
    let mut v___x_1791_: u32 = 0;
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_slice_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1808_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1771_) == 0 {
                    v_currPos_1781_ = leanh::lean_ctor_get(v_a_1771_, 0);
                    v_searcher_1782_ = leanh::lean_ctor_get(v_a_1771_, 1);
                    v_isSharedCheck_1808_ = (!leanh::lean_is_exclusive(v_a_1771_)) as u8;
                    if v_isSharedCheck_1808_ == 0 {
                        v___x_1784_ = v_a_1771_;
                        v_isShared_1785_ = v_isSharedCheck_1808_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_searcher_1782_);
                        leanh::lean_inc(v_currPos_1781_);
                        leanh::lean_dec(v_a_1771_);
                        v___x_1784_ = leanh::lean_box(0);
                        v_isShared_1785_ = v_isSharedCheck_1808_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_1770_);
                    leanh::lean_dec_ref(v_x_1768_);
                    return v_b_1772_;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_x_1768_);
                v___x_1777_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1777_, 0, v_x_1768_);
                leanh::lean_ctor_set(v___x_1777_, 1, v_startInclusive_1775_);
                leanh::lean_ctor_set(v___x_1777_, 2, v_endExclusive_1776_);
                v___x_1778_ = l_String_Slice_toString(v___x_1777_);
                leanh::lean_dec_ref_known(v___x_1777_, 3);
                v___x_1779_ = lean_array_push(v_b_1772_, v___x_1778_);
                v_a_1771_ = v_it_1774_;
                v_b_1772_ = v___x_1779_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1786_ = leanh::lean_ctor_get(v___x_1769_, 1);
                v_endExclusive_1787_ = leanh::lean_ctor_get(v___x_1769_, 2);
                v___x_1788_ = lean_nat_sub(v_endExclusive_1787_, v_startInclusive_1786_);
                v___x_1789_ = lean_nat_dec_eq(v_searcher_1782_, v___x_1788_);
                leanh::lean_dec(v___x_1788_);
                if v___x_1789_ == 0 {
                    v___x_1790_ = 47;
                    v___x_1791_ = lean_string_utf8_get_fast(v_x_1768_, v_searcher_1782_);
                    v___x_1792_ = lean_uint32_dec_eq(v___x_1791_, v___x_1790_);
                    if v___x_1792_ == 0 {
                        v___x_1793_ = lean_string_utf8_next_fast(v_x_1768_, v_searcher_1782_);
                        leanh::lean_dec(v_searcher_1782_);
                        if v_isShared_1785_ == 0 {
                            leanh::lean_ctor_set(v___x_1784_, 1, v___x_1793_);
                            v___x_1795_ = v___x_1784_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1797_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_currPos_1781_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1797_, 1, v___x_1793_);
                            v___x_1795_ = v_reuseFailAlloc_1797_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1798_ = lean_string_utf8_next_fast(v_x_1768_, v_searcher_1782_);
                        v___x_1799_ = lean_nat_sub(v___x_1798_, v_searcher_1782_);
                        v___x_1800_ = lean_nat_add(v_searcher_1782_, v___x_1799_);
                        leanh::lean_dec(v___x_1799_);
                        v_slice_1801_ = l_String_Slice_subslice_x21(
                            v___x_1769_,
                            v_currPos_1781_,
                            v_searcher_1782_,
                        );
                        leanh::lean_inc(v___x_1800_);
                        if v_isShared_1785_ == 0 {
                            leanh::lean_ctor_set(v___x_1784_, 1, v___x_1800_);
                            leanh::lean_ctor_set(v___x_1784_, 0, v___x_1800_);
                            v_nextIt_1803_ = v___x_1784_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1806_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 0, v___x_1800_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1800_);
                            v_nextIt_1803_ = v_reuseFailAlloc_1806_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1784_);
                    leanh::lean_dec(v_searcher_1782_);
                    v___x_1807_ = leanh::lean_box(1);
                    leanh::lean_inc(v___x_1770_);
                    v_it_1774_ = v___x_1807_;
                    v_startInclusive_1775_ = v_currPos_1781_;
                    v_endExclusive_1776_ = v___x_1770_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1771_ = v___x_1795_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1804_ = leanh::lean_ctor_get(v_slice_1801_, 0);
                leanh::lean_inc(v_startInclusive_1804_);
                v_endExclusive_1805_ = leanh::lean_ctor_get(v_slice_1801_, 1);
                leanh::lean_inc(v_endExclusive_1805_);
                leanh::lean_dec_ref(v_slice_1801_);
                v_it_1774_ = v_nextIt_1803_;
                v_startInclusive_1775_ = v_startInclusive_1804_;
                v_endExclusive_1776_ = v_endExclusive_1805_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg___boxed(
    mut v_x_1809_: *mut leanh::LeanObject,
    mut v___x_1810_: *mut leanh::LeanObject,
    mut v___x_1811_: *mut leanh::LeanObject,
    mut v_a_1812_: *mut leanh::LeanObject,
    mut v_b_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_1809_, v___x_1810_, v___x_1811_, v_a_1812_, v_b_1813_);
    leanh::lean_dec_ref(v___x_1810_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_SubExpr_Pos_fromString_x3f(
    mut v_x_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ss_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1840_: usize = 0;
    let mut v___x_1841_: usize = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1846_: u8 = 0;
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1850_: u8 = 0;
    let mut v_a_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1854_: u8 = 0;
    let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1859_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1826_ = l_Lean_SubExpr_Pos_toString___closed__0;
                v___x_1827_ = lean_string_dec_eq(v_x_1819_, v___x_1826_);
                if v___x_1827_ == 0 {
                    v___x_1828_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1829_ = lean_string_utf8_byte_size(v_x_1819_);
                    leanh::lean_inc_ref(v_x_1819_);
                    v___x_1830_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1830_, 0, v_x_1819_);
                    leanh::lean_ctor_set(v___x_1830_, 1, v___x_1828_);
                    leanh::lean_ctor_set(v___x_1830_, 2, v___x_1829_);
                    v___x_1831_ = l_String_Slice_splitToSubslice___at___00Lean_SubExpr_Pos_fromString_x3f_spec__1(v___x_1830_);
                    v___x_1832_ = l_Lean_SubExpr_Pos_fromString_x3f___closed__1;
                    v___x_1833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_1819_, v___x_1830_, v___x_1829_, v___x_1831_, v___x_1832_);
                    leanh::lean_dec_ref_known(v___x_1830_, 3);
                    v___x_1834_ = lean_array_to_list(v___x_1833_);
                    if leanh::lean_obj_tag(v___x_1834_) == 1 {
                        v_head_1835_ = leanh::lean_ctor_get(v___x_1834_, 0);
                        leanh::lean_inc(v_head_1835_);
                        v_tail_1836_ = leanh::lean_ctor_get(v___x_1834_, 1);
                        leanh::lean_inc(v_tail_1836_);
                        v___x_1837_ = l_Lean_SubExpr_Pos_fromString_x3f___closed__2;
                        v___x_1838_ = lean_string_dec_eq(v_head_1835_, v___x_1837_);
                        leanh::lean_dec(v_head_1835_);
                        if v___x_1838_ == 0 {
                            leanh::lean_dec(v_tail_1836_);
                            v_ss_1821_ = v___x_1834_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref_known(v___x_1834_, 2);
                            v___x_1839_ = lean_array_mk(v_tail_1836_);
                            v_sz_1840_ = lean_array_size(v___x_1839_);
                            v___x_1841_ = 0usize;
                            v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_SubExpr_Pos_fromString_x3f_spec__3(v_sz_1840_, v___x_1841_, v___x_1839_);
                            if leanh::lean_obj_tag(v___x_1842_) == 0 {
                                v_a_1843_ = leanh::lean_ctor_get(v___x_1842_, 0);
                                v_isSharedCheck_1850_ =
                                    (!leanh::lean_is_exclusive(v___x_1842_)) as u8;
                                if v_isSharedCheck_1850_ == 0 {
                                    v___x_1845_ = v___x_1842_;
                                    v_isShared_1846_ = v_isSharedCheck_1850_;
                                    state = 2;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1843_);
                                    leanh::lean_dec(v___x_1842_);
                                    v___x_1845_ = leanh::lean_box(0);
                                    v_isShared_1846_ = v_isSharedCheck_1850_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_1851_ = leanh::lean_ctor_get(v___x_1842_, 0);
                                v_isSharedCheck_1859_ =
                                    (!leanh::lean_is_exclusive(v___x_1842_)) as u8;
                                if v_isSharedCheck_1859_ == 0 {
                                    v___x_1853_ = v___x_1842_;
                                    v_isShared_1854_ = v_isSharedCheck_1859_;
                                    state = 4;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1851_);
                                    leanh::lean_dec(v___x_1842_);
                                    v___x_1853_ = leanh::lean_box(0);
                                    v_isShared_1854_ = v_isSharedCheck_1859_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_ss_1821_ = v___x_1834_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1819_);
                    v___x_1860_ =
                        l___private_Lean_SubExpr_0__Lean_SubExpr_Pos_ofStringCoord___closed__7;
                    return v___x_1860_;
                }
            }
            1 => {
                v___x_1822_ = l_Lean_SubExpr_Pos_fromString_x3f___closed__0;
                v___x_1823_ =
                    l_List_toString___at___00Lean_SubExpr_Pos_fromString_x3f_spec__0(v_ss_1821_);
                leanh::lean_dec(v_ss_1821_);
                v___x_1824_ = lean_string_append(v___x_1822_, v___x_1823_);
                leanh::lean_dec_ref(v___x_1823_);
                v___x_1825_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1825_, 0, v___x_1824_);
                return v___x_1825_;
            }
            2 => {
                if v_isShared_1846_ == 0 {
                    v___x_1848_ = v___x_1845_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1849_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
                    v___x_1848_ = v_reuseFailAlloc_1849_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1848_;
            }
            4 => {
                v___x_1855_ = l_Lean_SubExpr_Pos_ofArray(v_a_1851_);
                leanh::lean_dec(v_a_1851_);
                if v_isShared_1854_ == 0 {
                    leanh::lean_ctor_set(v___x_1853_, 0, v___x_1855_);
                    v___x_1857_ = v___x_1853_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1858_, 0, v___x_1855_);
                    v___x_1857_ = v_reuseFailAlloc_1858_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(
    mut v_x_1861_: *mut leanh::LeanObject,
    mut v___x_1862_: *mut leanh::LeanObject,
    mut v___x_1863_: *mut leanh::LeanObject,
    mut v_inst_1864_: *mut leanh::LeanObject,
    mut v_R_1865_: *mut leanh::LeanObject,
    mut v_a_1866_: *mut leanh::LeanObject,
    mut v_b_1867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___redArg(v_x_1861_, v___x_1862_, v___x_1863_, v_a_1866_, v_b_1867_);
    return v___x_1868_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2___boxed(
    mut v_x_1869_: *mut leanh::LeanObject,
    mut v___x_1870_: *mut leanh::LeanObject,
    mut v___x_1871_: *mut leanh::LeanObject,
    mut v_inst_1872_: *mut leanh::LeanObject,
    mut v_R_1873_: *mut leanh::LeanObject,
    mut v_a_1874_: *mut leanh::LeanObject,
    mut v_b_1875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1876_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_SubExpr_Pos_fromString_x3f_spec__2(v_x_1869_, v___x_1870_, v___x_1871_, v_inst_1872_, v_R_1873_, v_a_1874_, v_b_1875_);
    leanh::lean_dec_ref(v___x_1870_);
    return v_res_1876_;
}
pub unsafe fn l_Lean_SubExpr_Pos_fromString_x21(
    mut v_s_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1879_ = l_Lean_SubExpr_Pos_fromString_x3f(v_s_1878_);
    if leanh::lean_obj_tag(v___x_1879_) == 0 {
        let mut v_a_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1880_ = leanh::lean_ctor_get(v___x_1879_, 0);
        leanh::lean_inc(v_a_1880_);
        leanh::lean_dec_ref_known(v___x_1879_, 1);
        v___x_1881_ = l_Lean_SubExpr_Pos_head___closed__0;
        v___x_1882_ = l_Lean_SubExpr_Pos_fromString_x21___closed__0;
        v___x_1883_ = leanh::lean_unsigned_to_nat(142);
        v___x_1884_ = leanh::lean_unsigned_to_nat(16);
        v___x_1885_ = l_mkPanicMessageWithDecl(
            v___x_1881_,
            v___x_1882_,
            v___x_1883_,
            v___x_1884_,
            v_a_1880_,
        );
        leanh::lean_dec(v_a_1880_);
        v___x_1886_ = l_panic___at___00Lean_SubExpr_Pos_tail_spec__0(v___x_1885_);
        return v___x_1886_;
    } else {
        let mut v_a_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1887_ = leanh::lean_ctor_get(v___x_1879_, 0);
        leanh::lean_inc(v_a_1887_);
        leanh::lean_dec_ref_known(v___x_1879_, 1);
        return v_a_1887_;
    }
}
pub unsafe fn l_Lean_SubExpr_Pos_instDecidableEq(
    mut v_a_1890_: *mut leanh::LeanObject,
    mut v_b_1891_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1892_: u8 = 0;
    v___x_1892_ = lean_nat_dec_eq(v_a_1890_, v_b_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_SubExpr_Pos_instDecidableEq___boxed(
    mut v_a_1893_: *mut leanh::LeanObject,
    mut v_b_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1895_: u8 = 0;
    let mut v_r_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_Lean_SubExpr_Pos_instDecidableEq(v_a_1893_, v_b_1894_);
    leanh::lean_dec(v_b_1894_);
    leanh::lean_dec(v_a_1893_);
    v_r_1896_ = leanh::lean_box((v_res_1895_) as usize);
    return v_r_1896_;
}
pub unsafe fn _init_l_Lean_SubExpr_Pos_instEmptyCollection() -> *mut leanh::LeanObject {
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = leanh::lean_unsigned_to_nat(1);
    return v___x_1899_;
}
pub unsafe fn l_Lean_SubExpr_Pos_instRepr___lam__0(
    mut v_p_1903_: *mut leanh::LeanObject,
    mut v_x_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = l_Lean_SubExpr_Pos_instRepr___lam__0___closed__1;
    v___x_1906_ = l_Lean_SubExpr_Pos_toString(v_p_1903_);
    v___x_1907_ = l_String_quote(v___x_1906_);
    v___x_1908_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1908_, 0, v___x_1907_);
    v___x_1909_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1909_, 0, v___x_1905_);
    leanh::lean_ctor_set(v___x_1909_, 1, v___x_1908_);
    return v___x_1909_;
}
pub unsafe fn l_Lean_SubExpr_Pos_instRepr___lam__0___boxed(
    mut v_p_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1912_ = l_Lean_SubExpr_Pos_instRepr___lam__0(v_p_1910_, v_x_1911_);
    leanh::lean_dec(v_x_1911_);
    leanh::lean_dec(v_p_1910_);
    return v_res_1912_;
}
pub unsafe fn l_Lean_SubExpr_Pos_instToJson___lam__0(
    mut v_s_1915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1916_, 0, v_s_1915_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_SubExpr_Pos_instFromJson___lam__0(
    mut v_j_1922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1927_: u8 = 0;
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1931_: u8 = 0;
    let mut v_a_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1923_ = l_Lean_Json_getStr_x3f(v_j_1922_);
                if leanh::lean_obj_tag(v___x_1923_) == 0 {
                    v_a_1924_ = leanh::lean_ctor_get(v___x_1923_, 0);
                    v_isSharedCheck_1931_ = (!leanh::lean_is_exclusive(v___x_1923_)) as u8;
                    if v_isSharedCheck_1931_ == 0 {
                        v___x_1926_ = v___x_1923_;
                        v_isShared_1927_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1924_);
                        leanh::lean_dec(v___x_1923_);
                        v___x_1926_ = leanh::lean_box(0);
                        v_isShared_1927_ = v_isSharedCheck_1931_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1932_ = leanh::lean_ctor_get(v___x_1923_, 0);
                    leanh::lean_inc(v_a_1932_);
                    leanh::lean_dec_ref_known(v___x_1923_, 1);
                    v___x_1933_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_1932_);
                    return v___x_1933_;
                }
            }
            1 => {
                if v_isShared_1927_ == 0 {
                    v___x_1929_ = v___x_1926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1930_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_a_1924_);
                    v___x_1929_ = v_reuseFailAlloc_1930_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1929_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_instInhabitedSubExpr_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1939_ = leanh::lean_box(0);
    v___x_1940_ = l_Lean_instInhabitedSubExpr_default___closed__1;
    v___x_1941_ = l_Lean_Expr_const___override(v___x_1940_, v___x_1939_);
    return v___x_1941_;
}
pub unsafe fn _init_l_Lean_instInhabitedSubExpr_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1942_ = leanh::lean_unsigned_to_nat(1);
    v___x_1943_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedSubExpr_default___closed__2),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedSubExpr_default___closed__2_once),
        _init_l_Lean_instInhabitedSubExpr_default___closed__2,
    );
    v___x_1944_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1944_, 0, v___x_1943_);
    leanh::lean_ctor_set(v___x_1944_, 1, v___x_1942_);
    return v___x_1944_;
}
pub unsafe fn _init_l_Lean_instInhabitedSubExpr_default() -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instInhabitedSubExpr_default___closed__3),
        core::ptr::addr_of_mut!(l_Lean_instInhabitedSubExpr_default___closed__3_once),
        _init_l_Lean_instInhabitedSubExpr_default___closed__3,
    );
    return v___x_1945_;
}
pub unsafe fn _init_l_Lean_instInhabitedSubExpr() -> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = l_Lean_instInhabitedSubExpr_default;
    return v___x_1946_;
}
pub unsafe fn l_Lean_SubExpr_mkRoot(
    mut v_e_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1948_ = leanh::lean_unsigned_to_nat(1);
    v___x_1949_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1949_, 0, v_e_1947_);
    leanh::lean_ctor_set(v___x_1949_, 1, v___x_1948_);
    return v___x_1949_;
}
pub unsafe fn l_Lean_SubExpr_isRoot(mut v_s_1950_: *mut leanh::LeanObject) -> u8 {
    let mut v_pos_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: u8 = 0;
    v_pos_1951_ = leanh::lean_ctor_get(v_s_1950_, 1);
    v___x_1952_ = l_Lean_SubExpr_Pos_isRoot(v_pos_1951_);
    return v___x_1952_;
}
pub unsafe fn l_Lean_SubExpr_isRoot___boxed(
    mut v_s_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1954_: u8 = 0;
    let mut v_r_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1954_ = l_Lean_SubExpr_isRoot(v_s_1953_);
    leanh::lean_dec_ref(v_s_1953_);
    v_r_1955_ = leanh::lean_box((v_res_1954_) as usize);
    return v_r_1955_;
}
pub unsafe fn l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(
    mut v_msg_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_Lean_instInhabitedSubExpr_default;
    v___x_1958_ = lean_panic_fn_borrowed(v___x_1957_, v_msg_1956_);
    return v___x_1958_;
}
pub unsafe fn _init_l_Lean_SubExpr_bindingBody_x21___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_SubExpr_bindingBody_x21___closed__1;
    v___x_1962_ = leanh::lean_unsigned_to_nat(9);
    v___x_1963_ = leanh::lean_unsigned_to_nat(181);
    v___x_1964_ = l_Lean_SubExpr_bindingBody_x21___closed__0;
    v___x_1965_ = l_Lean_SubExpr_Pos_head___closed__0;
    v___x_1966_ = l_mkPanicMessageWithDecl(
        v___x_1965_,
        v___x_1964_,
        v___x_1963_,
        v___x_1962_,
        v___x_1961_,
    );
    return v___x_1966_;
}
pub unsafe fn l_Lean_SubExpr_bindingBody_x21(
    mut v_x_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_expr_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1972_: u8 = 0;
    let mut v_b_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_1968_ = leanh::lean_ctor_get(v_x_1967_, 0);
                v_pos_1969_ = leanh::lean_ctor_get(v_x_1967_, 1);
                v_isSharedCheck_1983_ = (!leanh::lean_is_exclusive(v_x_1967_)) as u8;
                if v_isSharedCheck_1983_ == 0 {
                    v___x_1971_ = v_x_1967_;
                    v_isShared_1972_ = v_isSharedCheck_1983_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_pos_1969_);
                    leanh::lean_inc(v_expr_1968_);
                    leanh::lean_dec(v_x_1967_);
                    v___x_1971_ = leanh::lean_box(0);
                    v_isShared_1972_ = v_isSharedCheck_1983_;
                    state = 1;
                    continue;
                }
            }
            1 => match leanh::lean_obj_tag(v_expr_1968_) {
                7 => {
                    v_body_1979_ = leanh::lean_ctor_get(v_expr_1968_, 2);
                    leanh::lean_inc_ref(v_body_1979_);
                    leanh::lean_dec_ref_known(v_expr_1968_, 3);
                    v_b_1974_ = v_body_1979_;
                    state = 2;
                    continue;
                }
                6 => {
                    v_body_1980_ = leanh::lean_ctor_get(v_expr_1968_, 2);
                    leanh::lean_inc_ref(v_body_1980_);
                    leanh::lean_dec_ref_known(v_expr_1968_, 3);
                    v_b_1974_ = v_body_1980_;
                    state = 2;
                    continue;
                }
                _ => {
                    leanh::lean_del_object(v___x_1971_);
                    leanh::lean_dec(v_pos_1969_);
                    leanh::lean_dec_ref(v_expr_1968_);
                    v___x_1981_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_SubExpr_bindingBody_x21___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_SubExpr_bindingBody_x21___closed__2_once),
                        _init_l_Lean_SubExpr_bindingBody_x21___closed__2,
                    );
                    v___x_1982_ =
                        l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_1981_);
                    return v___x_1982_;
                }
            },
            2 => {
                v___x_1975_ = l_Lean_SubExpr_Pos_pushBindingBody(v_pos_1969_);
                leanh::lean_dec(v_pos_1969_);
                if v_isShared_1972_ == 0 {
                    leanh::lean_ctor_set(v___x_1971_, 1, v___x_1975_);
                    leanh::lean_ctor_set(v___x_1971_, 0, v_b_1974_);
                    v___x_1977_ = v___x_1971_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1978_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_b_1974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1978_, 1, v___x_1975_);
                    v___x_1977_ = v_reuseFailAlloc_1978_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1977_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_SubExpr_bindingDomain_x21___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1985_ = l_Lean_SubExpr_bindingBody_x21___closed__1;
    v___x_1986_ = leanh::lean_unsigned_to_nat(9);
    v___x_1987_ = leanh::lean_unsigned_to_nat(186);
    v___x_1988_ = l_Lean_SubExpr_bindingDomain_x21___closed__0;
    v___x_1989_ = l_Lean_SubExpr_Pos_head___closed__0;
    v___x_1990_ = l_mkPanicMessageWithDecl(
        v___x_1989_,
        v___x_1988_,
        v___x_1987_,
        v___x_1986_,
        v___x_1985_,
    );
    return v___x_1990_;
}
pub unsafe fn l_Lean_SubExpr_bindingDomain_x21(
    mut v_x_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_expr_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v_t_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2007_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_expr_1992_ = leanh::lean_ctor_get(v_x_1991_, 0);
                v_pos_1993_ = leanh::lean_ctor_get(v_x_1991_, 1);
                v_isSharedCheck_2007_ = (!leanh::lean_is_exclusive(v_x_1991_)) as u8;
                if v_isSharedCheck_2007_ == 0 {
                    v___x_1995_ = v_x_1991_;
                    v_isShared_1996_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_pos_1993_);
                    leanh::lean_inc(v_expr_1992_);
                    leanh::lean_dec(v_x_1991_);
                    v___x_1995_ = leanh::lean_box(0);
                    v_isShared_1996_ = v_isSharedCheck_2007_;
                    state = 1;
                    continue;
                }
            }
            1 => match leanh::lean_obj_tag(v_expr_1992_) {
                7 => {
                    v_binderType_2003_ = leanh::lean_ctor_get(v_expr_1992_, 1);
                    leanh::lean_inc_ref(v_binderType_2003_);
                    leanh::lean_dec_ref_known(v_expr_1992_, 3);
                    v_t_1998_ = v_binderType_2003_;
                    state = 2;
                    continue;
                }
                6 => {
                    v_binderType_2004_ = leanh::lean_ctor_get(v_expr_1992_, 1);
                    leanh::lean_inc_ref(v_binderType_2004_);
                    leanh::lean_dec_ref_known(v_expr_1992_, 3);
                    v_t_1998_ = v_binderType_2004_;
                    state = 2;
                    continue;
                }
                _ => {
                    leanh::lean_del_object(v___x_1995_);
                    leanh::lean_dec(v_pos_1993_);
                    leanh::lean_dec_ref(v_expr_1992_);
                    v___x_2005_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_SubExpr_bindingDomain_x21___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_SubExpr_bindingDomain_x21___closed__1_once),
                        _init_l_Lean_SubExpr_bindingDomain_x21___closed__1,
                    );
                    v___x_2006_ =
                        l_panic___at___00Lean_SubExpr_bindingBody_x21_spec__0(v___x_2005_);
                    return v___x_2006_;
                }
            },
            2 => {
                v___x_1999_ = l_Lean_SubExpr_Pos_pushBindingDomain(v_pos_1993_);
                leanh::lean_dec(v_pos_1993_);
                if v_isShared_1996_ == 0 {
                    leanh::lean_ctor_set(v___x_1995_, 1, v___x_1999_);
                    leanh::lean_ctor_set(v___x_1995_, 0, v_t_1998_);
                    v___x_2001_ = v___x_1995_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_t_1998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_instToJsonFVarId___lam__0(
    mut v_f_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2009_: u8 = 0;
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = 1;
    v___x_2010_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_f_2008_, v___x_2009_);
    v___x_2011_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2011_, 0, v___x_2010_);
    return v___x_2011_;
}
pub unsafe fn l_Lean_SubExpr_instFromJsonFVarId___lam__0(
    mut v_j_2015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2020_: u8 = 0;
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2024_: u8 = 0;
    let mut v_a_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2016_ = l_Lean_Name_fromJson_x3f(v_j_2015_);
                if leanh::lean_obj_tag(v___x_2016_) == 0 {
                    v_a_2017_ = leanh::lean_ctor_get(v___x_2016_, 0);
                    v_isSharedCheck_2024_ = (!leanh::lean_is_exclusive(v___x_2016_)) as u8;
                    if v_isSharedCheck_2024_ == 0 {
                        v___x_2019_ = v___x_2016_;
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2017_);
                        leanh::lean_dec(v___x_2016_);
                        v___x_2019_ = leanh::lean_box(0);
                        v_isShared_2020_ = v_isSharedCheck_2024_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2025_ = leanh::lean_ctor_get(v___x_2016_, 0);
                    v_isSharedCheck_2032_ = (!leanh::lean_is_exclusive(v___x_2016_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v___x_2027_ = v___x_2016_;
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2025_);
                        leanh::lean_dec(v___x_2016_);
                        v___x_2027_ = leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2020_ == 0 {
                    v___x_2022_ = v___x_2019_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_a_2017_);
                    v___x_2022_ = v_reuseFailAlloc_2023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2022_;
            }
            3 => {
                if v_isShared_2028_ == 0 {
                    v___x_2030_ = v___x_2027_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
                    v___x_2030_ = v_reuseFailAlloc_2031_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_ctorIdx(
    mut v_x_2036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_2036_) {
        0 => {
            let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2037_ = leanh::lean_unsigned_to_nat(0);
            return v___x_2037_;
        }
        1 => {
            let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2038_ = leanh::lean_unsigned_to_nat(1);
            return v___x_2038_;
        }
        2 => {
            let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2039_ = leanh::lean_unsigned_to_nat(2);
            return v___x_2039_;
        }
        _ => {
            let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_2040_ = leanh::lean_unsigned_to_nat(3);
            return v___x_2040_;
        }
    }
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_ctorIdx___boxed(
    mut v_x_2041_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2042_ = l_Lean_SubExpr_GoalLocation_ctorIdx(v_x_2041_);
    leanh::lean_dec_ref(v_x_2041_);
    return v_res_2042_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_ctorElim___redArg(
    mut v_t_2043_: *mut leanh::LeanObject,
    mut v_k_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_2043_) {
        1 => {
            let mut v_a_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2045_ = leanh::lean_ctor_get(v_t_2043_, 0);
            leanh::lean_inc(v_a_2045_);
            v_a_2046_ = leanh::lean_ctor_get(v_t_2043_, 1);
            leanh::lean_inc(v_a_2046_);
            leanh::lean_dec_ref_known(v_t_2043_, 2);
            v___x_2047_ = leanh::lean_apply_2(v_k_2044_, v_a_2045_, v_a_2046_);
            return v___x_2047_;
        }
        2 => {
            let mut v_a_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2048_ = leanh::lean_ctor_get(v_t_2043_, 0);
            leanh::lean_inc(v_a_2048_);
            v_a_2049_ = leanh::lean_ctor_get(v_t_2043_, 1);
            leanh::lean_inc(v_a_2049_);
            leanh::lean_dec_ref_known(v_t_2043_, 2);
            v___x_2050_ = leanh::lean_apply_2(v_k_2044_, v_a_2048_, v_a_2049_);
            return v___x_2050_;
        }
        _ => {
            let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_2051_ = leanh::lean_ctor_get(v_t_2043_, 0);
            leanh::lean_inc(v_a_2051_);
            leanh::lean_dec_ref(v_t_2043_);
            v___x_2052_ = leanh::lean_apply_1(v_k_2044_, v_a_2051_);
            return v___x_2052_;
        }
    }
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_ctorElim(
    mut v_motive_2053_: *mut leanh::LeanObject,
    mut v_ctorIdx_2054_: *mut leanh::LeanObject,
    mut v_t_2055_: *mut leanh::LeanObject,
    mut v_h_2056_: *mut leanh::LeanObject,
    mut v_k_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2058_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2055_, v_k_2057_);
    return v___x_2058_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_ctorElim___boxed(
    mut v_motive_2059_: *mut leanh::LeanObject,
    mut v_ctorIdx_2060_: *mut leanh::LeanObject,
    mut v_t_2061_: *mut leanh::LeanObject,
    mut v_h_2062_: *mut leanh::LeanObject,
    mut v_k_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2064_ = l_Lean_SubExpr_GoalLocation_ctorElim(
        v_motive_2059_,
        v_ctorIdx_2060_,
        v_t_2061_,
        v_h_2062_,
        v_k_2063_,
    );
    leanh::lean_dec(v_ctorIdx_2060_);
    return v_res_2064_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hyp_elim___redArg(
    mut v_t_2065_: *mut leanh::LeanObject,
    mut v_hyp_2066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2065_, v_hyp_2066_);
    return v___x_2067_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hyp_elim(
    mut v_motive_2068_: *mut leanh::LeanObject,
    mut v_t_2069_: *mut leanh::LeanObject,
    mut v_h_2070_: *mut leanh::LeanObject,
    mut v_hyp_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2069_, v_hyp_2071_);
    return v___x_2072_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hypType_elim___redArg(
    mut v_t_2073_: *mut leanh::LeanObject,
    mut v_hypType_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2073_, v_hypType_2074_);
    return v___x_2075_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hypType_elim(
    mut v_motive_2076_: *mut leanh::LeanObject,
    mut v_t_2077_: *mut leanh::LeanObject,
    mut v_h_2078_: *mut leanh::LeanObject,
    mut v_hypType_2079_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2077_, v_hypType_2079_);
    return v___x_2080_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hypValue_elim___redArg(
    mut v_t_2081_: *mut leanh::LeanObject,
    mut v_hypValue_2082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2081_, v_hypValue_2082_);
    return v___x_2083_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_hypValue_elim(
    mut v_motive_2084_: *mut leanh::LeanObject,
    mut v_t_2085_: *mut leanh::LeanObject,
    mut v_h_2086_: *mut leanh::LeanObject,
    mut v_hypValue_2087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2088_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2085_, v_hypValue_2087_);
    return v___x_2088_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_target_elim___redArg(
    mut v_t_2089_: *mut leanh::LeanObject,
    mut v_target_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2091_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2089_, v_target_2090_);
    return v___x_2091_;
}
pub unsafe fn l_Lean_SubExpr_GoalLocation_target_elim(
    mut v_motive_2092_: *mut leanh::LeanObject,
    mut v_t_2093_: *mut leanh::LeanObject,
    mut v_h_2094_: *mut leanh::LeanObject,
    mut v_target_2095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = l_Lean_SubExpr_GoalLocation_ctorElim___redArg(v_t_2093_, v_target_2095_);
    return v___x_2096_;
}
pub unsafe fn l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(
    mut v_json_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2113_: u8 = 0;
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: u8 = 0;
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: u8 = 0;
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: u8 = 0;
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v_a_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2142_: u8 = 0;
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2146_: u8 = 0;
    let mut v_a_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_a_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_a_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2184_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut v_a_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_a_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2208_: u8 = 0;
    let mut v___x_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2212_: u8 = 0;
    let mut v_a_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2218_: u8 = 0;
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2222_: u8 = 0;
    let mut v_a_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2226_: u8 = 0;
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2231_: u8 = 0;
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2238_: u8 = 0;
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_a_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2250_: u8 = 0;
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2254_: u8 = 0;
    let mut v_a_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2258_: u8 = 0;
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2265_: u8 = 0;
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2272_: u8 = 0;
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2276_: u8 = 0;
    let mut v_a_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_a_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2298_: u8 = 0;
    let mut v_a_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2302_: u8 = 0;
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_json_2107_);
                v___x_2108_ = l_Lean_Json_getTag_x3f(v_json_2107_);
                if leanh::lean_obj_tag(v___x_2108_) == 0 {
                    leanh::lean_dec(v_json_2107_);
                    v___x_2109_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__1;
                    return v___x_2109_;
                } else {
                    v_val_2110_ = leanh::lean_ctor_get(v___x_2108_, 0);
                    v_isSharedCheck_2310_ = (!leanh::lean_is_exclusive(v___x_2108_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v___x_2112_ = v___x_2108_;
                        v_isShared_2113_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2110_);
                        leanh::lean_dec(v___x_2108_);
                        v___x_2112_ = leanh::lean_box(0);
                        v_isShared_2113_ = v_isSharedCheck_2310_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2114_ = leanh::lean_box(0);
                v___x_2115_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2;
                v___x_2116_ = lean_string_dec_eq(v_val_2110_, v___x_2115_);
                if v___x_2116_ == 0 {
                    v___x_2117_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3;
                    v___x_2118_ = lean_string_dec_eq(v_val_2110_, v___x_2117_);
                    if v___x_2118_ == 0 {
                        leanh::lean_del_object(v___x_2112_);
                        v___x_2119_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4;
                        v___x_2120_ = lean_string_dec_eq(v_val_2110_, v___x_2119_);
                        if v___x_2120_ == 0 {
                            v___x_2121_ =
                                l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5;
                            v___x_2122_ = lean_string_dec_eq(v_val_2110_, v___x_2121_);
                            leanh::lean_dec(v_val_2110_);
                            if v___x_2122_ == 0 {
                                leanh::lean_dec(v_json_2107_);
                                v___x_2123_ =
                                    l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__7;
                                return v___x_2123_;
                            } else {
                                v___x_2124_ = leanh::lean_unsigned_to_nat(2);
                                v___x_2125_ = leanh::lean_box(0);
                                v___x_2126_ = l_Lean_Json_parseCtorFields(
                                    v_json_2107_,
                                    v___x_2121_,
                                    v___x_2124_,
                                    v___x_2125_,
                                );
                                if leanh::lean_obj_tag(v___x_2126_) == 0 {
                                    v_a_2127_ = leanh::lean_ctor_get(v___x_2126_, 0);
                                    v_isSharedCheck_2134_ =
                                        (!leanh::lean_is_exclusive(v___x_2126_)) as u8;
                                    if v_isSharedCheck_2134_ == 0 {
                                        v___x_2129_ = v___x_2126_;
                                        v_isShared_2130_ = v_isSharedCheck_2134_;
                                        state = 2;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2127_);
                                        leanh::lean_dec(v___x_2126_);
                                        v___x_2129_ = leanh::lean_box(0);
                                        v_isShared_2130_ = v_isSharedCheck_2134_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_2135_ = leanh::lean_ctor_get(v___x_2126_, 0);
                                    leanh::lean_inc(v_a_2135_);
                                    leanh::lean_dec_ref_known(v___x_2126_, 1);
                                    v___x_2136_ = leanh::lean_unsigned_to_nat(0);
                                    v___x_2137_ = lean_array_get_borrowed(
                                        v___x_2114_,
                                        v_a_2135_,
                                        v___x_2136_,
                                    );
                                    leanh::lean_inc(v___x_2137_);
                                    v___x_2138_ = l_Lean_Name_fromJson_x3f(v___x_2137_);
                                    if leanh::lean_obj_tag(v___x_2138_) == 0 {
                                        leanh::lean_dec(v_a_2135_);
                                        v_a_2139_ = leanh::lean_ctor_get(v___x_2138_, 0);
                                        v_isSharedCheck_2146_ =
                                            (!leanh::lean_is_exclusive(v___x_2138_)) as u8;
                                        if v_isSharedCheck_2146_ == 0 {
                                            v___x_2141_ = v___x_2138_;
                                            v_isShared_2142_ = v_isSharedCheck_2146_;
                                            state = 4;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2139_);
                                            leanh::lean_dec(v___x_2138_);
                                            v___x_2141_ = leanh::lean_box(0);
                                            v_isShared_2142_ = v_isSharedCheck_2146_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v_a_2147_ = leanh::lean_ctor_get(v___x_2138_, 0);
                                        leanh::lean_inc(v_a_2147_);
                                        leanh::lean_dec_ref_known(v___x_2138_, 1);
                                        v___x_2148_ = leanh::lean_unsigned_to_nat(1);
                                        v___x_2149_ =
                                            lean_array_get(v___x_2114_, v_a_2135_, v___x_2148_);
                                        leanh::lean_dec(v_a_2135_);
                                        v___x_2150_ = l_Lean_Json_getStr_x3f(v___x_2149_);
                                        if leanh::lean_obj_tag(v___x_2150_) == 0 {
                                            leanh::lean_dec(v_a_2147_);
                                            v_a_2151_ = leanh::lean_ctor_get(v___x_2150_, 0);
                                            v_isSharedCheck_2158_ =
                                                (!leanh::lean_is_exclusive(v___x_2150_))
                                                    as u8;
                                            if v_isSharedCheck_2158_ == 0 {
                                                v___x_2153_ = v___x_2150_;
                                                v_isShared_2154_ = v_isSharedCheck_2158_;
                                                state = 6;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2151_);
                                                leanh::lean_dec(v___x_2150_);
                                                v___x_2153_ = leanh::lean_box(0);
                                                v_isShared_2154_ = v_isSharedCheck_2158_;
                                                state = 6;
                                                continue;
                                            }
                                        } else {
                                            v_a_2159_ = leanh::lean_ctor_get(v___x_2150_, 0);
                                            leanh::lean_inc(v_a_2159_);
                                            leanh::lean_dec_ref_known(v___x_2150_, 1);
                                            v___x_2160_ =
                                                l_Lean_SubExpr_Pos_fromString_x3f(v_a_2159_);
                                            if leanh::lean_obj_tag(v___x_2160_) == 0 {
                                                leanh::lean_dec(v_a_2147_);
                                                v_a_2161_ =
                                                    leanh::lean_ctor_get(v___x_2160_, 0);
                                                v_isSharedCheck_2168_ =
                                                    (!leanh::lean_is_exclusive(v___x_2160_))
                                                        as u8;
                                                if v_isSharedCheck_2168_ == 0 {
                                                    v___x_2163_ = v___x_2160_;
                                                    v_isShared_2164_ = v_isSharedCheck_2168_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2161_);
                                                    leanh::lean_dec(v___x_2160_);
                                                    v___x_2163_ = leanh::lean_box(0);
                                                    v_isShared_2164_ = v_isSharedCheck_2168_;
                                                    state = 8;
                                                    continue;
                                                }
                                            } else {
                                                v_a_2169_ =
                                                    leanh::lean_ctor_get(v___x_2160_, 0);
                                                v_isSharedCheck_2177_ =
                                                    (!leanh::lean_is_exclusive(v___x_2160_))
                                                        as u8;
                                                if v_isSharedCheck_2177_ == 0 {
                                                    v___x_2171_ = v___x_2160_;
                                                    v_isShared_2172_ = v_isSharedCheck_2177_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_2169_);
                                                    leanh::lean_dec(v___x_2160_);
                                                    v___x_2171_ = leanh::lean_box(0);
                                                    v_isShared_2172_ = v_isSharedCheck_2177_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_2110_);
                            v___x_2178_ = leanh::lean_unsigned_to_nat(2);
                            v___x_2179_ = leanh::lean_box(0);
                            v___x_2180_ = l_Lean_Json_parseCtorFields(
                                v_json_2107_,
                                v___x_2119_,
                                v___x_2178_,
                                v___x_2179_,
                            );
                            if leanh::lean_obj_tag(v___x_2180_) == 0 {
                                v_a_2181_ = leanh::lean_ctor_get(v___x_2180_, 0);
                                v_isSharedCheck_2188_ =
                                    (!leanh::lean_is_exclusive(v___x_2180_)) as u8;
                                if v_isSharedCheck_2188_ == 0 {
                                    v___x_2183_ = v___x_2180_;
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 12;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2181_);
                                    leanh::lean_dec(v___x_2180_);
                                    v___x_2183_ = leanh::lean_box(0);
                                    v_isShared_2184_ = v_isSharedCheck_2188_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                v_a_2189_ = leanh::lean_ctor_get(v___x_2180_, 0);
                                leanh::lean_inc(v_a_2189_);
                                leanh::lean_dec_ref_known(v___x_2180_, 1);
                                v___x_2190_ = leanh::lean_unsigned_to_nat(0);
                                v___x_2191_ =
                                    lean_array_get_borrowed(v___x_2114_, v_a_2189_, v___x_2190_);
                                leanh::lean_inc(v___x_2191_);
                                v___x_2192_ = l_Lean_Name_fromJson_x3f(v___x_2191_);
                                if leanh::lean_obj_tag(v___x_2192_) == 0 {
                                    leanh::lean_dec(v_a_2189_);
                                    v_a_2193_ = leanh::lean_ctor_get(v___x_2192_, 0);
                                    v_isSharedCheck_2200_ =
                                        (!leanh::lean_is_exclusive(v___x_2192_)) as u8;
                                    if v_isSharedCheck_2200_ == 0 {
                                        v___x_2195_ = v___x_2192_;
                                        v_isShared_2196_ = v_isSharedCheck_2200_;
                                        state = 14;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_2193_);
                                        leanh::lean_dec(v___x_2192_);
                                        v___x_2195_ = leanh::lean_box(0);
                                        v_isShared_2196_ = v_isSharedCheck_2200_;
                                        state = 14;
                                        continue;
                                    }
                                } else {
                                    v_a_2201_ = leanh::lean_ctor_get(v___x_2192_, 0);
                                    leanh::lean_inc(v_a_2201_);
                                    leanh::lean_dec_ref_known(v___x_2192_, 1);
                                    v___x_2202_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_2203_ =
                                        lean_array_get(v___x_2114_, v_a_2189_, v___x_2202_);
                                    leanh::lean_dec(v_a_2189_);
                                    v___x_2204_ = l_Lean_Json_getStr_x3f(v___x_2203_);
                                    if leanh::lean_obj_tag(v___x_2204_) == 0 {
                                        leanh::lean_dec(v_a_2201_);
                                        v_a_2205_ = leanh::lean_ctor_get(v___x_2204_, 0);
                                        v_isSharedCheck_2212_ =
                                            (!leanh::lean_is_exclusive(v___x_2204_)) as u8;
                                        if v_isSharedCheck_2212_ == 0 {
                                            v___x_2207_ = v___x_2204_;
                                            v_isShared_2208_ = v_isSharedCheck_2212_;
                                            state = 16;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_2205_);
                                            leanh::lean_dec(v___x_2204_);
                                            v___x_2207_ = leanh::lean_box(0);
                                            v_isShared_2208_ = v_isSharedCheck_2212_;
                                            state = 16;
                                            continue;
                                        }
                                    } else {
                                        v_a_2213_ = leanh::lean_ctor_get(v___x_2204_, 0);
                                        leanh::lean_inc(v_a_2213_);
                                        leanh::lean_dec_ref_known(v___x_2204_, 1);
                                        v___x_2214_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_2213_);
                                        if leanh::lean_obj_tag(v___x_2214_) == 0 {
                                            leanh::lean_dec(v_a_2201_);
                                            v_a_2215_ = leanh::lean_ctor_get(v___x_2214_, 0);
                                            v_isSharedCheck_2222_ =
                                                (!leanh::lean_is_exclusive(v___x_2214_))
                                                    as u8;
                                            if v_isSharedCheck_2222_ == 0 {
                                                v___x_2217_ = v___x_2214_;
                                                v_isShared_2218_ = v_isSharedCheck_2222_;
                                                state = 18;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2215_);
                                                leanh::lean_dec(v___x_2214_);
                                                v___x_2217_ = leanh::lean_box(0);
                                                v_isShared_2218_ = v_isSharedCheck_2222_;
                                                state = 18;
                                                continue;
                                            }
                                        } else {
                                            v_a_2223_ = leanh::lean_ctor_get(v___x_2214_, 0);
                                            v_isSharedCheck_2231_ =
                                                (!leanh::lean_is_exclusive(v___x_2214_))
                                                    as u8;
                                            if v_isSharedCheck_2231_ == 0 {
                                                v___x_2225_ = v___x_2214_;
                                                v_isShared_2226_ = v_isSharedCheck_2231_;
                                                state = 20;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_2223_);
                                                leanh::lean_dec(v___x_2214_);
                                                v___x_2225_ = leanh::lean_box(0);
                                                v_isShared_2226_ = v_isSharedCheck_2231_;
                                                state = 20;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_2110_);
                        v___x_2232_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2233_ = leanh::lean_box(0);
                        v___x_2234_ = l_Lean_Json_parseCtorFields(
                            v_json_2107_,
                            v___x_2117_,
                            v___x_2232_,
                            v___x_2233_,
                        );
                        if leanh::lean_obj_tag(v___x_2234_) == 0 {
                            leanh::lean_del_object(v___x_2112_);
                            v_a_2235_ = leanh::lean_ctor_get(v___x_2234_, 0);
                            v_isSharedCheck_2242_ =
                                (!leanh::lean_is_exclusive(v___x_2234_)) as u8;
                            if v_isSharedCheck_2242_ == 0 {
                                v___x_2237_ = v___x_2234_;
                                v_isShared_2238_ = v_isSharedCheck_2242_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2235_);
                                leanh::lean_dec(v___x_2234_);
                                v___x_2237_ = leanh::lean_box(0);
                                v_isShared_2238_ = v_isSharedCheck_2242_;
                                state = 22;
                                continue;
                            }
                        } else {
                            v_a_2243_ = leanh::lean_ctor_get(v___x_2234_, 0);
                            leanh::lean_inc(v_a_2243_);
                            leanh::lean_dec_ref_known(v___x_2234_, 1);
                            v___x_2244_ = leanh::lean_unsigned_to_nat(0);
                            v___x_2245_ = lean_array_get(v___x_2114_, v_a_2243_, v___x_2244_);
                            leanh::lean_dec(v_a_2243_);
                            v___x_2246_ = l_Lean_Name_fromJson_x3f(v___x_2245_);
                            if leanh::lean_obj_tag(v___x_2246_) == 0 {
                                leanh::lean_del_object(v___x_2112_);
                                v_a_2247_ = leanh::lean_ctor_get(v___x_2246_, 0);
                                v_isSharedCheck_2254_ =
                                    (!leanh::lean_is_exclusive(v___x_2246_)) as u8;
                                if v_isSharedCheck_2254_ == 0 {
                                    v___x_2249_ = v___x_2246_;
                                    v_isShared_2250_ = v_isSharedCheck_2254_;
                                    state = 24;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2247_);
                                    leanh::lean_dec(v___x_2246_);
                                    v___x_2249_ = leanh::lean_box(0);
                                    v_isShared_2250_ = v_isSharedCheck_2254_;
                                    state = 24;
                                    continue;
                                }
                            } else {
                                v_a_2255_ = leanh::lean_ctor_get(v___x_2246_, 0);
                                v_isSharedCheck_2265_ =
                                    (!leanh::lean_is_exclusive(v___x_2246_)) as u8;
                                if v_isSharedCheck_2265_ == 0 {
                                    v___x_2257_ = v___x_2246_;
                                    v_isShared_2258_ = v_isSharedCheck_2265_;
                                    state = 26;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2255_);
                                    leanh::lean_dec(v___x_2246_);
                                    v___x_2257_ = leanh::lean_box(0);
                                    v_isShared_2258_ = v_isSharedCheck_2265_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_2110_);
                    v___x_2266_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2267_ = leanh::lean_box(0);
                    v___x_2268_ = l_Lean_Json_parseCtorFields(
                        v_json_2107_,
                        v___x_2115_,
                        v___x_2266_,
                        v___x_2267_,
                    );
                    if leanh::lean_obj_tag(v___x_2268_) == 0 {
                        leanh::lean_del_object(v___x_2112_);
                        v_a_2269_ = leanh::lean_ctor_get(v___x_2268_, 0);
                        v_isSharedCheck_2276_ =
                            (!leanh::lean_is_exclusive(v___x_2268_)) as u8;
                        if v_isSharedCheck_2276_ == 0 {
                            v___x_2271_ = v___x_2268_;
                            v_isShared_2272_ = v_isSharedCheck_2276_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2269_);
                            leanh::lean_dec(v___x_2268_);
                            v___x_2271_ = leanh::lean_box(0);
                            v_isShared_2272_ = v_isSharedCheck_2276_;
                            state = 29;
                            continue;
                        }
                    } else {
                        v_a_2277_ = leanh::lean_ctor_get(v___x_2268_, 0);
                        leanh::lean_inc(v_a_2277_);
                        leanh::lean_dec_ref_known(v___x_2268_, 1);
                        v___x_2278_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2279_ = lean_array_get(v___x_2114_, v_a_2277_, v___x_2278_);
                        leanh::lean_dec(v_a_2277_);
                        v___x_2280_ = l_Lean_Json_getStr_x3f(v___x_2279_);
                        if leanh::lean_obj_tag(v___x_2280_) == 0 {
                            leanh::lean_del_object(v___x_2112_);
                            v_a_2281_ = leanh::lean_ctor_get(v___x_2280_, 0);
                            v_isSharedCheck_2288_ =
                                (!leanh::lean_is_exclusive(v___x_2280_)) as u8;
                            if v_isSharedCheck_2288_ == 0 {
                                v___x_2283_ = v___x_2280_;
                                v_isShared_2284_ = v_isSharedCheck_2288_;
                                state = 31;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2281_);
                                leanh::lean_dec(v___x_2280_);
                                v___x_2283_ = leanh::lean_box(0);
                                v_isShared_2284_ = v_isSharedCheck_2288_;
                                state = 31;
                                continue;
                            }
                        } else {
                            v_a_2289_ = leanh::lean_ctor_get(v___x_2280_, 0);
                            leanh::lean_inc(v_a_2289_);
                            leanh::lean_dec_ref_known(v___x_2280_, 1);
                            v___x_2290_ = l_Lean_SubExpr_Pos_fromString_x3f(v_a_2289_);
                            if leanh::lean_obj_tag(v___x_2290_) == 0 {
                                leanh::lean_del_object(v___x_2112_);
                                v_a_2291_ = leanh::lean_ctor_get(v___x_2290_, 0);
                                v_isSharedCheck_2298_ =
                                    (!leanh::lean_is_exclusive(v___x_2290_)) as u8;
                                if v_isSharedCheck_2298_ == 0 {
                                    v___x_2293_ = v___x_2290_;
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 33;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2291_);
                                    leanh::lean_dec(v___x_2290_);
                                    v___x_2293_ = leanh::lean_box(0);
                                    v_isShared_2294_ = v_isSharedCheck_2298_;
                                    state = 33;
                                    continue;
                                }
                            } else {
                                v_a_2299_ = leanh::lean_ctor_get(v___x_2290_, 0);
                                v_isSharedCheck_2309_ =
                                    (!leanh::lean_is_exclusive(v___x_2290_)) as u8;
                                if v_isSharedCheck_2309_ == 0 {
                                    v___x_2301_ = v___x_2290_;
                                    v_isShared_2302_ = v_isSharedCheck_2309_;
                                    state = 35;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2299_);
                                    leanh::lean_dec(v___x_2290_);
                                    v___x_2301_ = leanh::lean_box(0);
                                    v_isShared_2302_ = v_isSharedCheck_2309_;
                                    state = 35;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2130_ == 0 {
                    v___x_2132_ = v___x_2129_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
                    v___x_2132_ = v_reuseFailAlloc_2133_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2132_;
            }
            4 => {
                if v_isShared_2142_ == 0 {
                    v___x_2144_ = v___x_2141_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2145_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
                    v___x_2144_ = v_reuseFailAlloc_2145_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2144_;
            }
            6 => {
                if v_isShared_2154_ == 0 {
                    v___x_2156_ = v___x_2153_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2157_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2156_;
            }
            8 => {
                if v_isShared_2164_ == 0 {
                    v___x_2166_ = v___x_2163_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2167_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
                    v___x_2166_ = v_reuseFailAlloc_2167_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2166_;
            }
            10 => {
                v___x_2173_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2173_, 0, v_a_2147_);
                leanh::lean_ctor_set(v___x_2173_, 1, v_a_2169_);
                if v_isShared_2172_ == 0 {
                    leanh::lean_ctor_set(v___x_2171_, 0, v___x_2173_);
                    v___x_2175_ = v___x_2171_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2176_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2173_);
                    v___x_2175_ = v_reuseFailAlloc_2176_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2175_;
            }
            12 => {
                if v_isShared_2184_ == 0 {
                    v___x_2186_ = v___x_2183_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
                    v___x_2186_ = v_reuseFailAlloc_2187_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2186_;
            }
            14 => {
                if v_isShared_2196_ == 0 {
                    v___x_2198_ = v___x_2195_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
                    v___x_2198_ = v_reuseFailAlloc_2199_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2198_;
            }
            16 => {
                if v_isShared_2208_ == 0 {
                    v___x_2210_ = v___x_2207_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2211_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
                    v___x_2210_ = v_reuseFailAlloc_2211_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2210_;
            }
            18 => {
                if v_isShared_2218_ == 0 {
                    v___x_2220_ = v___x_2217_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2221_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
                    v___x_2220_ = v_reuseFailAlloc_2221_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2220_;
            }
            20 => {
                v___x_2227_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2227_, 0, v_a_2201_);
                leanh::lean_ctor_set(v___x_2227_, 1, v_a_2223_);
                if v_isShared_2226_ == 0 {
                    leanh::lean_ctor_set(v___x_2225_, 0, v___x_2227_);
                    v___x_2229_ = v___x_2225_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2230_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
                    v___x_2229_ = v_reuseFailAlloc_2230_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2229_;
            }
            22 => {
                if v_isShared_2238_ == 0 {
                    v___x_2240_ = v___x_2237_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2235_);
                    v___x_2240_ = v_reuseFailAlloc_2241_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2240_;
            }
            24 => {
                if v_isShared_2250_ == 0 {
                    v___x_2252_ = v___x_2249_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
                    v___x_2252_ = v_reuseFailAlloc_2253_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2252_;
            }
            26 => {
                if v_isShared_2113_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2112_, 0);
                    leanh::lean_ctor_set(v___x_2112_, 0, v_a_2255_);
                    v___x_2260_ = v___x_2112_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_2264_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_a_2255_);
                    v___x_2260_ = v_reuseFailAlloc_2264_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_2258_ == 0 {
                    leanh::lean_ctor_set(v___x_2257_, 0, v___x_2260_);
                    v___x_2262_ = v___x_2257_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2260_);
                    v___x_2262_ = v_reuseFailAlloc_2263_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2262_;
            }
            29 => {
                if v_isShared_2272_ == 0 {
                    v___x_2274_ = v___x_2271_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2275_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
                    v___x_2274_ = v_reuseFailAlloc_2275_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2274_;
            }
            31 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2287_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2286_;
            }
            33 => {
                if v_isShared_2294_ == 0 {
                    v___x_2296_ = v___x_2293_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_a_2291_);
                    v___x_2296_ = v_reuseFailAlloc_2297_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_2296_;
            }
            35 => {
                if v_isShared_2113_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2112_, 3);
                    leanh::lean_ctor_set(v___x_2112_, 0, v_a_2299_);
                    v___x_2304_ = v___x_2112_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2299_);
                    v___x_2304_ = v_reuseFailAlloc_2308_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_2302_ == 0 {
                    leanh::lean_ctor_set(v___x_2301_, 0, v___x_2304_);
                    v___x_2306_ = v___x_2301_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
                    v___x_2306_ = v_reuseFailAlloc_2307_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_instToJsonGoalLocation_toJson(
    mut v_x_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2317_: u8 = 0;
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: u8 = 0;
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut v_a_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2333_: u8 = 0;
    let mut v___x_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2351_: u8 = 0;
    let mut v_a_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_a_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2388_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2313_) {
                0 => {
                    v_a_2314_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    v_isSharedCheck_2328_ = (!leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2316_ = v_x_2313_;
                        v_isShared_2317_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2314_);
                        leanh::lean_dec(v_x_2313_);
                        v___x_2316_ = leanh::lean_box(0);
                        v_isShared_2317_ = v_isSharedCheck_2328_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_a_2329_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    v_a_2330_ = leanh::lean_ctor_get(v_x_2313_, 1);
                    v_isSharedCheck_2351_ = (!leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2351_ == 0 {
                        v___x_2332_ = v_x_2313_;
                        v_isShared_2333_ = v_isSharedCheck_2351_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2330_);
                        leanh::lean_inc(v_a_2329_);
                        leanh::lean_dec(v_x_2313_);
                        v___x_2332_ = leanh::lean_box(0);
                        v_isShared_2333_ = v_isSharedCheck_2351_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_a_2352_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    v_a_2353_ = leanh::lean_ctor_get(v_x_2313_, 1);
                    v_isSharedCheck_2374_ = (!leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2374_ == 0 {
                        v___x_2355_ = v_x_2313_;
                        v_isShared_2356_ = v_isSharedCheck_2374_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2353_);
                        leanh::lean_inc(v_a_2352_);
                        leanh::lean_dec(v_x_2313_);
                        v___x_2355_ = leanh::lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2374_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_a_2375_ = leanh::lean_ctor_get(v_x_2313_, 0);
                    v_isSharedCheck_2388_ = (!leanh::lean_is_exclusive(v_x_2313_)) as u8;
                    if v_isSharedCheck_2388_ == 0 {
                        v___x_2377_ = v_x_2313_;
                        v_isShared_2378_ = v_isSharedCheck_2388_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2375_);
                        leanh::lean_dec(v_x_2313_);
                        v___x_2377_ = leanh::lean_box(0);
                        v_isShared_2378_ = v_isSharedCheck_2388_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2318_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__3;
                v___x_2319_ = 1;
                v___x_2320_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_a_2314_,
                    v___x_2319_,
                );
                if v_isShared_2317_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2316_, 3);
                    leanh::lean_ctor_set(v___x_2316_, 0, v___x_2320_);
                    v___x_2322_ = v___x_2316_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v___x_2320_);
                    v___x_2322_ = v_reuseFailAlloc_2327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2323_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2323_, 0, v___x_2318_);
                leanh::lean_ctor_set(v___x_2323_, 1, v___x_2322_);
                v___x_2324_ = leanh::lean_box(0);
                v___x_2325_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2325_, 0, v___x_2323_);
                leanh::lean_ctor_set(v___x_2325_, 1, v___x_2324_);
                v___x_2326_ = l_Lean_Json_mkObj(v___x_2325_);
                leanh::lean_dec_ref_known(v___x_2325_, 2);
                return v___x_2326_;
            }
            3 => {
                v___x_2334_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__4;
                v___x_2335_ = 1;
                v___x_2336_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_a_2329_,
                    v___x_2335_,
                );
                v___x_2337_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2337_, 0, v___x_2336_);
                v___x_2338_ = l_Lean_SubExpr_Pos_toString(v_a_2330_);
                leanh::lean_dec(v_a_2330_);
                v___x_2339_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2339_, 0, v___x_2338_);
                v___x_2340_ = leanh::lean_unsigned_to_nat(2);
                v___x_2341_ = lean_mk_empty_array_with_capacity(v___x_2340_);
                v___x_2342_ = lean_array_push(v___x_2341_, v___x_2337_);
                v___x_2343_ = lean_array_push(v___x_2342_, v___x_2339_);
                v___x_2344_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2344_, 0, v___x_2343_);
                if v_isShared_2333_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2332_, 0);
                    leanh::lean_ctor_set(v___x_2332_, 1, v___x_2344_);
                    leanh::lean_ctor_set(v___x_2332_, 0, v___x_2334_);
                    v___x_2346_ = v___x_2332_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2350_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2334_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_2344_);
                    v___x_2346_ = v_reuseFailAlloc_2350_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2347_ = leanh::lean_box(0);
                v___x_2348_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2348_, 0, v___x_2346_);
                leanh::lean_ctor_set(v___x_2348_, 1, v___x_2347_);
                v___x_2349_ = l_Lean_Json_mkObj(v___x_2348_);
                leanh::lean_dec_ref_known(v___x_2348_, 2);
                return v___x_2349_;
            }
            5 => {
                v___x_2357_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__5;
                v___x_2358_ = 1;
                v___x_2359_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_a_2352_,
                    v___x_2358_,
                );
                v___x_2360_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2360_, 0, v___x_2359_);
                v___x_2361_ = l_Lean_SubExpr_Pos_toString(v_a_2353_);
                leanh::lean_dec(v_a_2353_);
                v___x_2362_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2362_, 0, v___x_2361_);
                v___x_2363_ = leanh::lean_unsigned_to_nat(2);
                v___x_2364_ = lean_mk_empty_array_with_capacity(v___x_2363_);
                v___x_2365_ = lean_array_push(v___x_2364_, v___x_2360_);
                v___x_2366_ = lean_array_push(v___x_2365_, v___x_2362_);
                v___x_2367_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2367_, 0, v___x_2366_);
                if v_isShared_2356_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2355_, 0);
                    leanh::lean_ctor_set(v___x_2355_, 1, v___x_2367_);
                    leanh::lean_ctor_set(v___x_2355_, 0, v___x_2357_);
                    v___x_2369_ = v___x_2355_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 0, v___x_2357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2373_, 1, v___x_2367_);
                    v___x_2369_ = v_reuseFailAlloc_2373_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2370_ = leanh::lean_box(0);
                v___x_2371_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2371_, 0, v___x_2369_);
                leanh::lean_ctor_set(v___x_2371_, 1, v___x_2370_);
                v___x_2372_ = l_Lean_Json_mkObj(v___x_2371_);
                leanh::lean_dec_ref_known(v___x_2371_, 2);
                return v___x_2372_;
            }
            7 => {
                v___x_2379_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson___closed__2;
                v___x_2380_ = l_Lean_SubExpr_Pos_toString(v_a_2375_);
                leanh::lean_dec(v_a_2375_);
                if v_isShared_2378_ == 0 {
                    leanh::lean_ctor_set(v___x_2377_, 0, v___x_2380_);
                    v___x_2382_ = v___x_2377_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2387_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2380_);
                    v___x_2382_ = v_reuseFailAlloc_2387_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2383_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2383_, 0, v___x_2379_);
                leanh::lean_ctor_set(v___x_2383_, 1, v___x_2382_);
                v___x_2384_ = leanh::lean_box(0);
                v___x_2385_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2385_, 0, v___x_2383_);
                leanh::lean_ctor_set(v___x_2385_, 1, v___x_2384_);
                v___x_2386_ = l_Lean_Json_mkObj(v___x_2385_);
                leanh::lean_dec_ref_known(v___x_2385_, 2);
                return v___x_2386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(
    mut v_j_2391_: *mut leanh::LeanObject,
    mut v_k_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2398_: u8 = 0;
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2402_: u8 = 0;
    let mut v_a_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2393_ = l_Lean_Json_getObjValD(v_j_2391_, v_k_2392_);
                v___x_2394_ = l_Lean_Name_fromJson_x3f(v___x_2393_);
                if leanh::lean_obj_tag(v___x_2394_) == 0 {
                    v_a_2395_ = leanh::lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2402_ = (!leanh::lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2402_ == 0 {
                        v___x_2397_ = v___x_2394_;
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2395_);
                        leanh::lean_dec(v___x_2394_);
                        v___x_2397_ = leanh::lean_box(0);
                        v_isShared_2398_ = v_isSharedCheck_2402_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2403_ = leanh::lean_ctor_get(v___x_2394_, 0);
                    v_isSharedCheck_2410_ = (!leanh::lean_is_exclusive(v___x_2394_)) as u8;
                    if v_isSharedCheck_2410_ == 0 {
                        v___x_2405_ = v___x_2394_;
                        v_isShared_2406_ = v_isSharedCheck_2410_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2403_);
                        leanh::lean_dec(v___x_2394_);
                        v___x_2405_ = leanh::lean_box(0);
                        v_isShared_2406_ = v_isSharedCheck_2410_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2398_ == 0 {
                    v___x_2400_ = v___x_2397_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
                    v___x_2400_ = v_reuseFailAlloc_2401_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2400_;
            }
            3 => {
                if v_isShared_2406_ == 0 {
                    v___x_2408_ = v___x_2405_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2409_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
                    v___x_2408_ = v_reuseFailAlloc_2409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0___boxed(
    mut v_j_2411_: *mut leanh::LeanObject,
    mut v_k_2412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_j_2411_, v_k_2412_);
    leanh::lean_dec_ref(v_k_2412_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(
    mut v_j_2414_: *mut leanh::LeanObject,
    mut v_k_2415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Lean_Json_getObjValD(v_j_2414_, v_k_2415_);
    v___x_2417_ = l_Lean_SubExpr_instFromJsonGoalLocation_fromJson(v___x_2416_);
    return v___x_2417_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1___boxed(
    mut v_j_2418_: *mut leanh::LeanObject,
    mut v_k_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_j_2418_, v_k_2419_);
    leanh::lean_dec_ref(v_k_2419_);
    return v_res_2420_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = 1;
    v___x_2430_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__4;
    v___x_2431_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2430_, v___x_2429_);
    return v___x_2431_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2433_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__6;
    v___x_2434_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5),
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5_once),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__5,
    );
    v___x_2435_ = lean_string_append(v___x_2434_, v___x_2433_);
    return v___x_2435_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2438_: u8 = 0;
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2438_ = 1;
    v___x_2439_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__8;
    v___x_2440_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2439_, v___x_2438_);
    return v___x_2440_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2441_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9_once),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__9,
    );
    v___x_2442_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7,
    );
    v___x_2443_ = lean_string_append(v___x_2442_, v___x_2441_);
    return v___x_2443_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2445_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11;
    v___x_2446_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10),
        core::ptr::addr_of_mut!(
            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10_once
        ),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__10,
    );
    v___x_2447_ = lean_string_append(v___x_2446_, v___x_2445_);
    return v___x_2447_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2451_: u8 = 0;
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2451_ = 1;
    v___x_2452_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__14;
    v___x_2453_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_2452_, v___x_2451_);
    return v___x_2453_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2454_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15),
        core::ptr::addr_of_mut!(
            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15_once
        ),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__15,
    );
    v___x_2455_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7),
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7_once),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__7,
    );
    v___x_2456_ = lean_string_append(v___x_2455_, v___x_2454_);
    return v___x_2456_;
}
pub unsafe fn _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2457_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__11;
    v___x_2458_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16),
        core::ptr::addr_of_mut!(
            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16_once
        ),
        _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__16,
    );
    v___x_2459_ = lean_string_append(v___x_2458_, v___x_2457_);
    return v___x_2459_;
}
pub unsafe fn l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson(
    mut v_json_2460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2466_: u8 = 0;
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2472_: u8 = 0;
    let mut v_a_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2480_: u8 = 0;
    let mut v_a_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v_a_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2497_: u8 = 0;
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2501_: u8 = 0;
    let mut v_a_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2461_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0;
                leanh::lean_inc(v_json_2460_);
                v___x_2462_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__0(v_json_2460_, v___x_2461_);
                if leanh::lean_obj_tag(v___x_2462_) == 0 {
                    leanh::lean_dec(v_json_2460_);
                    v_a_2463_ = leanh::lean_ctor_get(v___x_2462_, 0);
                    v_isSharedCheck_2472_ = (!leanh::lean_is_exclusive(v___x_2462_)) as u8;
                    if v_isSharedCheck_2472_ == 0 {
                        v___x_2465_ = v___x_2462_;
                        v_isShared_2466_ = v_isSharedCheck_2472_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2463_);
                        leanh::lean_dec(v___x_2462_);
                        v___x_2465_ = leanh::lean_box(0);
                        v_isShared_2466_ = v_isSharedCheck_2472_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_2462_) == 0 {
                        leanh::lean_dec(v_json_2460_);
                        v_a_2473_ = leanh::lean_ctor_get(v___x_2462_, 0);
                        v_isSharedCheck_2480_ =
                            (!leanh::lean_is_exclusive(v___x_2462_)) as u8;
                        if v_isSharedCheck_2480_ == 0 {
                            v___x_2475_ = v___x_2462_;
                            v_isShared_2476_ = v_isSharedCheck_2480_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2473_);
                            leanh::lean_dec(v___x_2462_);
                            v___x_2475_ = leanh::lean_box(0);
                            v_isShared_2476_ = v_isSharedCheck_2480_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2481_ = leanh::lean_ctor_get(v___x_2462_, 0);
                        leanh::lean_inc(v_a_2481_);
                        leanh::lean_dec_ref_known(v___x_2462_, 1);
                        v___x_2482_ =
                            l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13;
                        v___x_2483_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_SubExpr_instFromJsonGoalsLocation_fromJson_spec__1(v_json_2460_, v___x_2482_);
                        if leanh::lean_obj_tag(v___x_2483_) == 0 {
                            leanh::lean_dec(v_a_2481_);
                            v_a_2484_ = leanh::lean_ctor_get(v___x_2483_, 0);
                            v_isSharedCheck_2493_ =
                                (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                            if v_isSharedCheck_2493_ == 0 {
                                v___x_2486_ = v___x_2483_;
                                v_isShared_2487_ = v_isSharedCheck_2493_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2484_);
                                leanh::lean_dec(v___x_2483_);
                                v___x_2486_ = leanh::lean_box(0);
                                v_isShared_2487_ = v_isSharedCheck_2493_;
                                state = 5;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_2483_) == 0 {
                                leanh::lean_dec(v_a_2481_);
                                v_a_2494_ = leanh::lean_ctor_get(v___x_2483_, 0);
                                v_isSharedCheck_2501_ =
                                    (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                                if v_isSharedCheck_2501_ == 0 {
                                    v___x_2496_ = v___x_2483_;
                                    v_isShared_2497_ = v_isSharedCheck_2501_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2494_);
                                    leanh::lean_dec(v___x_2483_);
                                    v___x_2496_ = leanh::lean_box(0);
                                    v_isShared_2497_ = v_isSharedCheck_2501_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v_a_2502_ = leanh::lean_ctor_get(v___x_2483_, 0);
                                v_isSharedCheck_2510_ =
                                    (!leanh::lean_is_exclusive(v___x_2483_)) as u8;
                                if v_isSharedCheck_2510_ == 0 {
                                    v___x_2504_ = v___x_2483_;
                                    v_isShared_2505_ = v_isSharedCheck_2510_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2502_);
                                    leanh::lean_dec(v___x_2483_);
                                    v___x_2504_ = leanh::lean_box(0);
                                    v_isShared_2505_ = v_isSharedCheck_2510_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2467_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12_once
                    ),
                    _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__12,
                );
                v___x_2468_ = lean_string_append(v___x_2467_, v_a_2463_);
                leanh::lean_dec(v_a_2463_);
                if v_isShared_2466_ == 0 {
                    leanh::lean_ctor_set(v___x_2465_, 0, v___x_2468_);
                    v___x_2470_ = v___x_2465_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2471_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
                    v___x_2470_ = v_reuseFailAlloc_2471_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2470_;
            }
            3 => {
                if v_isShared_2476_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2475_, 0);
                    v___x_2478_ = v___x_2475_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2479_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
                    v___x_2478_ = v_reuseFailAlloc_2479_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2478_;
            }
            5 => {
                v___x_2488_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17_once
                    ),
                    _init_l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__17,
                );
                v___x_2489_ = lean_string_append(v___x_2488_, v_a_2484_);
                leanh::lean_dec(v_a_2484_);
                if v_isShared_2487_ == 0 {
                    leanh::lean_ctor_set(v___x_2486_, 0, v___x_2489_);
                    v___x_2491_ = v___x_2486_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2489_);
                    v___x_2491_ = v_reuseFailAlloc_2492_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2491_;
            }
            7 => {
                if v_isShared_2497_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2496_, 0);
                    v___x_2499_ = v___x_2496_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2500_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
                    v___x_2499_ = v_reuseFailAlloc_2500_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2499_;
            }
            9 => {
                v___x_2506_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2506_, 0, v_a_2481_);
                leanh::lean_ctor_set(v___x_2506_, 1, v_a_2502_);
                if v_isShared_2505_ == 0 {
                    leanh::lean_ctor_set(v___x_2504_, 0, v___x_2506_);
                    v___x_2508_ = v___x_2504_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2509_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2509_, 0, v___x_2506_);
                    v___x_2508_ = v_reuseFailAlloc_2509_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2513_) == 0 {
                    v___x_2515_ = lean_array_to_list(v_a_2514_);
                    return v___x_2515_;
                } else {
                    v_head_2516_ = leanh::lean_ctor_get(v_a_2513_, 0);
                    leanh::lean_inc(v_head_2516_);
                    v_tail_2517_ = leanh::lean_ctor_get(v_a_2513_, 1);
                    leanh::lean_inc(v_tail_2517_);
                    leanh::lean_dec_ref_known(v_a_2513_, 2);
                    v___x_2518_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_2514_,
                        v_head_2516_,
                    );
                    v_a_2513_ = v_tail_2517_;
                    v_a_2514_ = v___x_2518_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_SubExpr_instToJsonGoalsLocation_toJson(
    mut v_x_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_mvarId_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_loc_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2527_: u8 = 0;
    let mut v___x_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_mvarId_2523_ = leanh::lean_ctor_get(v_x_2522_, 0);
                v_loc_2524_ = leanh::lean_ctor_get(v_x_2522_, 1);
                v_isSharedCheck_2546_ = (!leanh::lean_is_exclusive(v_x_2522_)) as u8;
                if v_isSharedCheck_2546_ == 0 {
                    v___x_2526_ = v_x_2522_;
                    v_isShared_2527_ = v_isSharedCheck_2546_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_loc_2524_);
                    leanh::lean_inc(v_mvarId_2523_);
                    leanh::lean_dec(v_x_2522_);
                    v___x_2526_ = leanh::lean_box(0);
                    v_isShared_2527_ = v_isSharedCheck_2546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2528_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__0;
                v___x_2529_ = 1;
                v___x_2530_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_mvarId_2523_,
                    v___x_2529_,
                );
                v___x_2531_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2531_, 0, v___x_2530_);
                if v_isShared_2527_ == 0 {
                    leanh::lean_ctor_set(v___x_2526_, 1, v___x_2531_);
                    leanh::lean_ctor_set(v___x_2526_, 0, v___x_2528_);
                    v___x_2533_ = v___x_2526_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___x_2528_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 1, v___x_2531_);
                    v___x_2533_ = v_reuseFailAlloc_2545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2534_ = leanh::lean_box(0);
                v___x_2535_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2535_, 0, v___x_2533_);
                leanh::lean_ctor_set(v___x_2535_, 1, v___x_2534_);
                v___x_2536_ = l_Lean_SubExpr_instFromJsonGoalsLocation_fromJson___closed__13;
                v___x_2537_ = l_Lean_SubExpr_instToJsonGoalLocation_toJson(v_loc_2524_);
                v___x_2538_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2538_, 0, v___x_2536_);
                leanh::lean_ctor_set(v___x_2538_, 1, v___x_2537_);
                v___x_2539_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2539_, 0, v___x_2538_);
                leanh::lean_ctor_set(v___x_2539_, 1, v___x_2534_);
                v___x_2540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2540_, 0, v___x_2539_);
                leanh::lean_ctor_set(v___x_2540_, 1, v___x_2534_);
                v___x_2541_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2541_, 0, v___x_2535_);
                leanh::lean_ctor_set(v___x_2541_, 1, v___x_2540_);
                v___x_2542_ = l_Lean_SubExpr_instToJsonGoalsLocation_toJson___closed__0;
                v___x_2543_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_SubExpr_instToJsonGoalsLocation_toJson_spec__0(v___x_2541_, v___x_2542_);
                v___x_2544_ = l_Lean_Json_mkObj(v___x_2543_);
                leanh::lean_dec(v___x_2543_);
                return v___x_2544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_traverseAppWithPos___redArg___lam__0(
    mut v_p_2549_: *mut leanh::LeanObject,
    mut v_visit_2550_: *mut leanh::LeanObject,
    mut v_arg_2551_: *mut leanh::LeanObject,
    mut v_x_2552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_SubExpr_Pos_pushAppArg(v_p_2549_);
    v___x_2554_ = leanh::lean_apply_2(v_visit_2550_, v___x_2553_, v_arg_2551_);
    return v___x_2554_;
}
pub unsafe fn l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed(
    mut v_p_2555_: *mut leanh::LeanObject,
    mut v_visit_2556_: *mut leanh::LeanObject,
    mut v_arg_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lean_Expr_traverseAppWithPos___redArg___lam__0(
        v_p_2555_,
        v_visit_2556_,
        v_arg_2557_,
        v_x_2558_,
    );
    leanh::lean_dec(v_p_2555_);
    return v_res_2559_;
}
pub unsafe fn l_Lean_Expr_traverseAppWithPos___redArg(
    mut v_inst_2560_: *mut leanh::LeanObject,
    mut v_visit_2561_: *mut leanh::LeanObject,
    mut v_p_2562_: *mut leanh::LeanObject,
    mut v_e_2563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_e_2563_) == 5 {
        let mut v_toApplicative_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toFunctor_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toSeq_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_fn_2567_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_arg_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_map_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toApplicative_2564_ = leanh::lean_ctor_get(v_inst_2560_, 0);
        v_toFunctor_2565_ = leanh::lean_ctor_get(v_toApplicative_2564_, 0);
        v_toSeq_2566_ = leanh::lean_ctor_get(v_toApplicative_2564_, 2);
        leanh::lean_inc(v_toSeq_2566_);
        v_fn_2567_ = leanh::lean_ctor_get(v_e_2563_, 0);
        leanh::lean_inc_ref(v_fn_2567_);
        v_arg_2568_ = leanh::lean_ctor_get(v_e_2563_, 1);
        v_map_2569_ = leanh::lean_ctor_get(v_toFunctor_2565_, 0);
        leanh::lean_inc(v_map_2569_);
        leanh::lean_inc_ref(v_arg_2568_);
        leanh::lean_inc(v_visit_2561_);
        leanh::lean_inc(v_p_2562_);
        v___f_2570_ = leanh::lean_alloc_closure(
            l_Lean_Expr_traverseAppWithPos___redArg___lam__0___boxed as *mut core::ffi::c_void,
            4,
            3,
        );
        leanh::lean_closure_set(v___f_2570_, 0, v_p_2562_);
        leanh::lean_closure_set(v___f_2570_, 1, v_visit_2561_);
        leanh::lean_closure_set(v___f_2570_, 2, v_arg_2568_);
        v___x_2571_ = leanh::lean_alloc_closure(
            l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl___boxed as *mut core::ffi::c_void,
            3,
            1,
        );
        leanh::lean_closure_set(v___x_2571_, 0, v_e_2563_);
        v___x_2572_ = l_Lean_SubExpr_Pos_pushAppFn(v_p_2562_);
        leanh::lean_dec(v_p_2562_);
        v___x_2573_ = l_Lean_Expr_traverseAppWithPos___redArg(
            v_inst_2560_,
            v_visit_2561_,
            v___x_2572_,
            v_fn_2567_,
        );
        v___x_2574_ = leanh::lean_apply_4(
            v_map_2569_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2571_,
            v___x_2573_,
        );
        v___x_2575_ = leanh::lean_apply_4(
            v_toSeq_2566_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2574_,
            v___f_2570_,
        );
        return v___x_2575_;
    } else {
        let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2560_);
        v___x_2576_ = leanh::lean_apply_2(v_visit_2561_, v_p_2562_, v_e_2563_);
        return v___x_2576_;
    }
}
pub unsafe fn l_Lean_Expr_traverseAppWithPos(
    mut v_M_2577_: *mut leanh::LeanObject,
    mut v_inst_2578_: *mut leanh::LeanObject,
    mut v_visit_2579_: *mut leanh::LeanObject,
    mut v_p_2580_: *mut leanh::LeanObject,
    mut v_e_2581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2582_ =
        l_Lean_Expr_traverseAppWithPos___redArg(v_inst_2578_, v_visit_2579_, v_p_2580_, v_e_2581_);
    return v___x_2582_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_SubExpr(builtin: u8) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_SubExpr_Pos_maxChildren = _init_l_Lean_SubExpr_Pos_maxChildren();
    leanh::lean_mark_persistent(l_Lean_SubExpr_Pos_maxChildren);
    l_Lean_SubExpr_Pos_typeCoord = _init_l_Lean_SubExpr_Pos_typeCoord();
    leanh::lean_mark_persistent(l_Lean_SubExpr_Pos_typeCoord);
    l_Lean_SubExpr_Pos_root = _init_l_Lean_SubExpr_Pos_root();
    leanh::lean_mark_persistent(l_Lean_SubExpr_Pos_root);
    l_Lean_SubExpr_Pos_instInhabited = _init_l_Lean_SubExpr_Pos_instInhabited();
    leanh::lean_mark_persistent(l_Lean_SubExpr_Pos_instInhabited);
    l_Lean_SubExpr_Pos_instEmptyCollection = _init_l_Lean_SubExpr_Pos_instEmptyCollection();
    leanh::lean_mark_persistent(l_Lean_SubExpr_Pos_instEmptyCollection);
    l_Lean_instInhabitedSubExpr_default = _init_l_Lean_instInhabitedSubExpr_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedSubExpr_default);
    l_Lean_instInhabitedSubExpr = _init_l_Lean_instInhabitedSubExpr();
    leanh::lean_mark_persistent(l_Lean_instInhabitedSubExpr);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_SubExpr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_SubExpr(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_Format_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_SubExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_SubExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_SubExpr(builtin);
}