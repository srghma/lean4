// Lean compiler output
// Module: Lean.Data.KVMap
// Imports: Init.Data.Format.Syntax Init.Data.ToString.Name Init.Data.ToString.Extra
use crate::ffi::{
    lean_int_dec_eq, lean_int_dec_lt, lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_to_int, lean_string_dec_eq, lean_string_length,
};
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::Format::Syntax::{
    initialize_Init_Data_Format_Syntax, l_Lean_Syntax_formatStx,
    runtime_initialize_Init_Data_Format_Syntax,
};
use crate::r#gen::Init::Data::Int::Repr::l_Int_repr;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::List::Control::l_List_forIn_x27_loop___redArg;
use crate::r#gen::Init::Data::Repr::{
    l_Bool_repr___redArg, l_Nat_reprFast, l_Repr_addAppParen, l_String_quote,
};
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringProd___redArg___lam__0;
use crate::r#gen::Init::Data::ToString::Extra::{
    initialize_Init_Data_ToString_Extra, l_List_toString___redArg,
    runtime_initialize_Init_Data_ToString_Extra,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name, l_Lean_Name_instToString___lam__0,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Name_reprPrec, l_Lean_Syntax_instRepr_repr, l_Lean_Syntax_structEq,
};
use crate::r#gen::Init::Prelude::{l_List_lengthTR___redArg, l_id___boxed};
pub static l_Lean_instInhabitedDataValue_default___closed__0_value: leanh::LeanStringObject<
    1,
> = leanh::LeanStringObject {
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
static mut l_Lean_instInhabitedDataValue_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instInhabitedDataValue_default___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_instInhabitedDataValue_default___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedDataValue_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instBEqDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqDataValue_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDataValue___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDataValue___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__0_value: leanh::LeanStringObject<24> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 83, 116,
            114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprDataValue_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDataValue_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprDataValue_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDataValue_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDataValue_repr___closed__5_value: leanh::LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 66, 111,
            111, 108, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__6_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__8_value: leanh::LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 78, 97,
            109, 101, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__9_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__10_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__9_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__11_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 78, 97,
            116, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__12_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__11_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__13_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__12_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__14_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 73, 110,
            116, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__15_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__14_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__16_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__15_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprDataValue_repr___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprDataValue_repr___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprDataValue_repr___closed__18_value: leanh::LeanStringObject<24> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 83, 121,
            110, 116, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__19_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__18_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__20_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__19_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprDataValue_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instReprDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_DataValue_str___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_DataValue_str___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_DataValue_str___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_DataValue_str___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_DataValue_str___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_DataValue_str___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_instToStringDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: lean_data_value_to_string as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToStringDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instToStringDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeStringDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeStringDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeStringDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeStringDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeBoolDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeBoolDataValue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeBoolDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeBoolDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeNameDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeNameDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeNameDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeNameDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeNatDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeNatDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeNatDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeNatDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeIntDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeIntDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeIntDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeIntDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instCoeSyntaxDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeSyntaxDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeSyntaxDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instCoeSyntaxDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instInhabitedKVMap_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedKVMap: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value) as *mut leanh::LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value:
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
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value:
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
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value:
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
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value:
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
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value
) as *mut leanh::LeanObject;
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value:
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
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value
) as *mut leanh::LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value:
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
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value
    ) as *mut leanh::LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value
) as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__0_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__1_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 110, 116, 114, 105, 101, 115, 0],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__2_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__3_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__4_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__5_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__4_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__6_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprKVMap_repr___redArg___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprKVMap_repr___redArg___closed__8_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_instReprKVMap_repr___redArg___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_instReprKVMap_repr___redArg___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instReprKVMap_repr___redArg___closed__11_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__12_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__8_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_instReprKVMap___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instReprKVMap_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instReprKVMap___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instReprKVMap: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instToString___closed__1_value: leanh::LeanClosureObject<2> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 2,
        m_objs: [
            core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instToString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instToString___closed__2_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Lean_KVMap_instToString___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instToString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_empty: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_KVMap_instBEq___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_eqv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instBEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instBEq: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instBEq___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueDataValue___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__1_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_KVMap_instValueDataValue___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__1_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueDataValue___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueDataValue: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueBool___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueBool___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueBool___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueNat___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueNat___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueInt___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueInt___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueInt___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueName___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueName___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueName___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueName___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueName: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueString___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueString___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueSyntax___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueSyntax___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueSyntax___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_KVMap_instValueSyntax___closed__1_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_KVMap_instValueSyntax___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__1_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_KVMap_instValueSyntax: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_DataValue_ctorIdx(
    mut v_x_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1152_) {
        0 => {
            let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1153_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1153_;
        }
        1 => {
            let mut v___x_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1154_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1154_;
        }
        2 => {
            let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1155_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1155_;
        }
        3 => {
            let mut v___x_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1156_ = leanh::lean_unsigned_to_nat(3);
            return v___x_1156_;
        }
        4 => {
            let mut v___x_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1157_ = leanh::lean_unsigned_to_nat(4);
            return v___x_1157_;
        }
        _ => {
            let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1158_ = leanh::lean_unsigned_to_nat(5);
            return v___x_1158_;
        }
    }
}
pub unsafe fn l_Lean_DataValue_ctorIdx___boxed(
    mut v_x_1159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_DataValue_ctorIdx(v_x_1159_);
    leanh::lean_dec_ref(v_x_1159_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_DataValue_ctorElim___redArg(
    mut v_t_1161_: *mut leanh::LeanObject,
    mut v_k_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_1161_) {
        0 => {
            let mut v_v_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1163_ = leanh::lean_ctor_get(v_t_1161_, 0);
            leanh::lean_inc_ref(v_v_1163_);
            leanh::lean_dec_ref_known(v_t_1161_, 1);
            v___x_1164_ = leanh::lean_apply_1(v_k_1162_, v_v_1163_);
            return v___x_1164_;
        }
        1 => {
            let mut v_v_1165_: u8 = 0;
            let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1165_ = leanh::lean_ctor_get_uint8(v_t_1161_, 0 as u32);
            leanh::lean_dec_ref_known(v_t_1161_, 0);
            v___x_1166_ = leanh::lean_box((v_v_1165_) as usize);
            v___x_1167_ = leanh::lean_apply_1(v_k_1162_, v___x_1166_);
            return v___x_1167_;
        }
        _ => {
            let mut v_v_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1168_ = leanh::lean_ctor_get(v_t_1161_, 0);
            leanh::lean_inc(v_v_1168_);
            leanh::lean_dec_ref(v_t_1161_);
            v___x_1169_ = leanh::lean_apply_1(v_k_1162_, v_v_1168_);
            return v___x_1169_;
        }
    }
}
pub unsafe fn l_Lean_DataValue_ctorElim(
    mut v_motive_1170_: *mut leanh::LeanObject,
    mut v_ctorIdx_1171_: *mut leanh::LeanObject,
    mut v_t_1172_: *mut leanh::LeanObject,
    mut v_h_1173_: *mut leanh::LeanObject,
    mut v_k_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_DataValue_ctorElim___redArg(v_t_1172_, v_k_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_DataValue_ctorElim___boxed(
    mut v_motive_1176_: *mut leanh::LeanObject,
    mut v_ctorIdx_1177_: *mut leanh::LeanObject,
    mut v_t_1178_: *mut leanh::LeanObject,
    mut v_h_1179_: *mut leanh::LeanObject,
    mut v_k_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_DataValue_ctorElim(
        v_motive_1176_,
        v_ctorIdx_1177_,
        v_t_1178_,
        v_h_1179_,
        v_k_1180_,
    );
    leanh::lean_dec(v_ctorIdx_1177_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_DataValue_ofString_elim___redArg(
    mut v_t_1182_: *mut leanh::LeanObject,
    mut v_ofString_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1184_ = l_Lean_DataValue_ctorElim___redArg(v_t_1182_, v_ofString_1183_);
    return v___x_1184_;
}
pub unsafe fn l_Lean_DataValue_ofString_elim(
    mut v_motive_1185_: *mut leanh::LeanObject,
    mut v_t_1186_: *mut leanh::LeanObject,
    mut v_h_1187_: *mut leanh::LeanObject,
    mut v_ofString_1188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lean_DataValue_ctorElim___redArg(v_t_1186_, v_ofString_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Lean_DataValue_ofBool_elim___redArg(
    mut v_t_1190_: *mut leanh::LeanObject,
    mut v_ofBool_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Lean_DataValue_ctorElim___redArg(v_t_1190_, v_ofBool_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Lean_DataValue_ofBool_elim(
    mut v_motive_1193_: *mut leanh::LeanObject,
    mut v_t_1194_: *mut leanh::LeanObject,
    mut v_h_1195_: *mut leanh::LeanObject,
    mut v_ofBool_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Lean_DataValue_ctorElim___redArg(v_t_1194_, v_ofBool_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Lean_DataValue_ofName_elim___redArg(
    mut v_t_1198_: *mut leanh::LeanObject,
    mut v_ofName_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Lean_DataValue_ctorElim___redArg(v_t_1198_, v_ofName_1199_);
    return v___x_1200_;
}
pub unsafe fn l_Lean_DataValue_ofName_elim(
    mut v_motive_1201_: *mut leanh::LeanObject,
    mut v_t_1202_: *mut leanh::LeanObject,
    mut v_h_1203_: *mut leanh::LeanObject,
    mut v_ofName_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Lean_DataValue_ctorElim___redArg(v_t_1202_, v_ofName_1204_);
    return v___x_1205_;
}
pub unsafe fn l_Lean_DataValue_ofNat_elim___redArg(
    mut v_t_1206_: *mut leanh::LeanObject,
    mut v_ofNat_1207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_DataValue_ctorElim___redArg(v_t_1206_, v_ofNat_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_DataValue_ofNat_elim(
    mut v_motive_1209_: *mut leanh::LeanObject,
    mut v_t_1210_: *mut leanh::LeanObject,
    mut v_h_1211_: *mut leanh::LeanObject,
    mut v_ofNat_1212_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Lean_DataValue_ctorElim___redArg(v_t_1210_, v_ofNat_1212_);
    return v___x_1213_;
}
pub unsafe fn l_Lean_DataValue_ofInt_elim___redArg(
    mut v_t_1214_: *mut leanh::LeanObject,
    mut v_ofInt_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_DataValue_ctorElim___redArg(v_t_1214_, v_ofInt_1215_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_DataValue_ofInt_elim(
    mut v_motive_1217_: *mut leanh::LeanObject,
    mut v_t_1218_: *mut leanh::LeanObject,
    mut v_h_1219_: *mut leanh::LeanObject,
    mut v_ofInt_1220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lean_DataValue_ctorElim___redArg(v_t_1218_, v_ofInt_1220_);
    return v___x_1221_;
}
pub unsafe fn l_Lean_DataValue_ofSyntax_elim___redArg(
    mut v_t_1222_: *mut leanh::LeanObject,
    mut v_ofSyntax_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_Lean_DataValue_ctorElim___redArg(v_t_1222_, v_ofSyntax_1223_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_DataValue_ofSyntax_elim(
    mut v_motive_1225_: *mut leanh::LeanObject,
    mut v_t_1226_: *mut leanh::LeanObject,
    mut v_h_1227_: *mut leanh::LeanObject,
    mut v_ofSyntax_1228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_DataValue_ctorElim___redArg(v_t_1226_, v_ofSyntax_1228_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_instBEqDataValue_beq(
    mut v_x_1235_: *mut leanh::LeanObject,
    mut v_x_1236_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1235_) {
        0 => {
            if leanh::lean_obj_tag(v_x_1236_) == 0 {
                let mut v_v_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_v_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1239_: u8 = 0;
                v_v_1237_ = leanh::lean_ctor_get(v_x_1235_, 0);
                leanh::lean_inc_ref(v_v_1237_);
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                v_v_1238_ = leanh::lean_ctor_get(v_x_1236_, 0);
                leanh::lean_inc_ref(v_v_1238_);
                leanh::lean_dec_ref_known(v_x_1236_, 1);
                v___x_1239_ = lean_string_dec_eq(v_v_1237_, v_v_1238_);
                leanh::lean_dec_ref(v_v_1238_);
                leanh::lean_dec_ref(v_v_1237_);
                return v___x_1239_;
            } else {
                let mut v___x_1240_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1240_ = 0;
                return v___x_1240_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_1236_) == 1 {
                let mut v_v_1241_: u8 = 0;
                v_v_1241_ = leanh::lean_ctor_get_uint8(v_x_1235_, 0 as u32);
                leanh::lean_dec_ref_known(v_x_1235_, 0);
                if v_v_1241_ == 0 {
                    let mut v_v_1242_: u8 = 0;
                    v_v_1242_ = leanh::lean_ctor_get_uint8(v_x_1236_, 0 as u32);
                    leanh::lean_dec_ref_known(v_x_1236_, 0);
                    if v_v_1242_ == 0 {
                        let mut v___x_1243_: u8 = 0;
                        v___x_1243_ = 1;
                        return v___x_1243_;
                    } else {
                        return v_v_1241_;
                    }
                } else {
                    let mut v_v_1244_: u8 = 0;
                    v_v_1244_ = leanh::lean_ctor_get_uint8(v_x_1236_, 0 as u32);
                    leanh::lean_dec_ref_known(v_x_1236_, 0);
                    return v_v_1244_;
                }
            } else {
                let mut v___x_1245_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 0);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1245_ = 0;
                return v___x_1245_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_1236_) == 2 {
                let mut v_v_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_v_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: u8 = 0;
                v_v_1246_ = leanh::lean_ctor_get(v_x_1235_, 0);
                leanh::lean_inc(v_v_1246_);
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                v_v_1247_ = leanh::lean_ctor_get(v_x_1236_, 0);
                leanh::lean_inc(v_v_1247_);
                leanh::lean_dec_ref_known(v_x_1236_, 1);
                v___x_1248_ = lean_name_eq(v_v_1246_, v_v_1247_);
                leanh::lean_dec(v_v_1247_);
                leanh::lean_dec(v_v_1246_);
                return v___x_1248_;
            } else {
                let mut v___x_1249_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1249_ = 0;
                return v___x_1249_;
            }
        }
        3 => {
            if leanh::lean_obj_tag(v_x_1236_) == 3 {
                let mut v_v_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_v_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1252_: u8 = 0;
                v_v_1250_ = leanh::lean_ctor_get(v_x_1235_, 0);
                leanh::lean_inc(v_v_1250_);
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                v_v_1251_ = leanh::lean_ctor_get(v_x_1236_, 0);
                leanh::lean_inc(v_v_1251_);
                leanh::lean_dec_ref_known(v_x_1236_, 1);
                v___x_1252_ = lean_nat_dec_eq(v_v_1250_, v_v_1251_);
                leanh::lean_dec(v_v_1251_);
                leanh::lean_dec(v_v_1250_);
                return v___x_1252_;
            } else {
                let mut v___x_1253_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1253_ = 0;
                return v___x_1253_;
            }
        }
        4 => {
            if leanh::lean_obj_tag(v_x_1236_) == 4 {
                let mut v_v_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_v_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1256_: u8 = 0;
                v_v_1254_ = leanh::lean_ctor_get(v_x_1235_, 0);
                leanh::lean_inc(v_v_1254_);
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                v_v_1255_ = leanh::lean_ctor_get(v_x_1236_, 0);
                leanh::lean_inc(v_v_1255_);
                leanh::lean_dec_ref_known(v_x_1236_, 1);
                v___x_1256_ = lean_int_dec_eq(v_v_1254_, v_v_1255_);
                leanh::lean_dec(v_v_1255_);
                leanh::lean_dec(v_v_1254_);
                return v___x_1256_;
            } else {
                let mut v___x_1257_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1257_ = 0;
                return v___x_1257_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_1236_) == 5 {
                let mut v_v_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_v_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1260_: u8 = 0;
                v_v_1258_ = leanh::lean_ctor_get(v_x_1235_, 0);
                leanh::lean_inc(v_v_1258_);
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                v_v_1259_ = leanh::lean_ctor_get(v_x_1236_, 0);
                leanh::lean_inc(v_v_1259_);
                leanh::lean_dec_ref_known(v_x_1236_, 1);
                v___x_1260_ = l_Lean_Syntax_structEq(v_v_1258_, v_v_1259_);
                return v___x_1260_;
            } else {
                let mut v___x_1261_: u8 = 0;
                leanh::lean_dec_ref_known(v_x_1235_, 1);
                leanh::lean_dec_ref(v_x_1236_);
                v___x_1261_ = 0;
                return v___x_1261_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqDataValue_beq___boxed(
    mut v_x_1262_: *mut leanh::LeanObject,
    mut v_x_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1264_: u8 = 0;
    let mut v_r_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1264_ = l_Lean_instBEqDataValue_beq(v_x_1262_, v_x_1263_);
    v_r_1265_ = leanh::lean_box((v_res_1264_) as usize);
    return v_r_1265_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1274_ = leanh::lean_unsigned_to_nat(2);
    v___x_1275_ = lean_nat_to_int(v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = leanh::lean_unsigned_to_nat(1);
    v___x_1277_ = lean_nat_to_int(v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__17() -> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = leanh::lean_unsigned_to_nat(0);
    v___x_1303_ = lean_nat_to_int(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Lean_instReprDataValue_repr(
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v_prec_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___y_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v_v_1342_: u8 = 0;
    let mut v___y_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___y_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut v_v_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v___y_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v_v_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1310_) {
                0 => {
                    v_v_1321_ = leanh::lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1341_ = (!leanh::lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1323_ = v_x_1310_;
                        v_isShared_1324_ = v_isSharedCheck_1341_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1321_);
                        leanh::lean_dec(v_x_1310_);
                        v___x_1323_ = leanh::lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1341_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_v_1342_ = leanh::lean_ctor_get_uint8(v_x_1310_, 0 as u32);
                    leanh::lean_dec_ref_known(v_x_1310_, 0);
                    v___x_1352_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1353_ = lean_nat_dec_le(v___x_1352_, v_prec_1311_);
                    if v___x_1353_ == 0 {
                        v___x_1354_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1344_ = v___x_1354_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1355_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                            _init_l_Lean_instReprDataValue_repr___closed__4,
                        );
                        v___y_1344_ = v___x_1355_;
                        state = 5;
                        continue;
                    }
                }
                2 => {
                    v_v_1356_ = leanh::lean_ctor_get(v_x_1310_, 0);
                    leanh::lean_inc(v_v_1356_);
                    leanh::lean_dec_ref_known(v_x_1310_, 1);
                    v___x_1367_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1368_ = lean_nat_dec_le(v___x_1367_, v_prec_1311_);
                    if v___x_1368_ == 0 {
                        v___x_1369_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1358_ = v___x_1369_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1370_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                            _init_l_Lean_instReprDataValue_repr___closed__4,
                        );
                        v___y_1358_ = v___x_1370_;
                        state = 6;
                        continue;
                    }
                }
                3 => {
                    v_v_1371_ = leanh::lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1391_ = (!leanh::lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1391_ == 0 {
                        v___x_1373_ = v_x_1310_;
                        v_isShared_1374_ = v_isSharedCheck_1391_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1371_);
                        leanh::lean_dec(v_x_1310_);
                        v___x_1373_ = leanh::lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1391_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_v_1392_ = leanh::lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1415_ = (!leanh::lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1394_ = v_x_1310_;
                        v_isShared_1395_ = v_isSharedCheck_1415_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_1392_);
                        leanh::lean_dec(v_x_1310_);
                        v___x_1394_ = leanh::lean_box(0);
                        v_isShared_1395_ = v_isSharedCheck_1415_;
                        state = 10;
                        continue;
                    }
                }
                _ => {
                    v_v_1416_ = leanh::lean_ctor_get(v_x_1310_, 0);
                    leanh::lean_inc(v_v_1416_);
                    leanh::lean_dec_ref_known(v_x_1310_, 1);
                    v___x_1427_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1428_ = lean_nat_dec_le(v___x_1427_, v_prec_1311_);
                    if v___x_1428_ == 0 {
                        v___x_1429_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1418_ = v___x_1429_;
                        state = 14;
                        continue;
                    } else {
                        v___x_1430_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                            _init_l_Lean_instReprDataValue_repr___closed__4,
                        );
                        v___y_1418_ = v___x_1430_;
                        state = 14;
                        continue;
                    }
                }
            },
            1 => {
                leanh::lean_inc(v___y_1314_);
                v___x_1316_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1316_, 0, v___y_1314_);
                leanh::lean_ctor_set(v___x_1316_, 1, v___y_1315_);
                leanh::lean_inc(v___y_1313_);
                v___x_1317_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1317_, 0, v___y_1313_);
                leanh::lean_ctor_set(v___x_1317_, 1, v___x_1316_);
                v___x_1318_ = 0;
                v___x_1319_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1319_, 0, v___x_1317_);
                leanh::lean_ctor_set_uint8(
                    v___x_1319_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1318_,
                );
                v___x_1320_ = l_Repr_addAppParen(v___x_1319_, v_prec_1311_);
                return v___x_1320_;
            }
            2 => {
                v___x_1337_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1338_ = lean_nat_dec_le(v___x_1337_, v_prec_1311_);
                if v___x_1338_ == 0 {
                    v___x_1339_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1326_ = v___x_1339_;
                    state = 3;
                    continue;
                } else {
                    v___x_1340_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                        _init_l_Lean_instReprDataValue_repr___closed__4,
                    );
                    v___y_1326_ = v___x_1340_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1327_ = l_Lean_instReprDataValue_repr___closed__2;
                v___x_1328_ = l_String_quote(v_v_1321_);
                if v_isShared_1324_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1323_, 3);
                    leanh::lean_ctor_set(v___x_1323_, 0, v___x_1328_);
                    v___x_1330_ = v___x_1323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
                    v___x_1330_ = v_reuseFailAlloc_1336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1331_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1331_, 0, v___x_1327_);
                leanh::lean_ctor_set(v___x_1331_, 1, v___x_1330_);
                leanh::lean_inc(v___y_1326_);
                v___x_1332_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1332_, 0, v___y_1326_);
                leanh::lean_ctor_set(v___x_1332_, 1, v___x_1331_);
                v___x_1333_ = 0;
                v___x_1334_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1334_, 0, v___x_1332_);
                leanh::lean_ctor_set_uint8(
                    v___x_1334_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1333_,
                );
                v___x_1335_ = l_Repr_addAppParen(v___x_1334_, v_prec_1311_);
                return v___x_1335_;
            }
            5 => {
                v___x_1345_ = l_Lean_instReprDataValue_repr___closed__7;
                v___x_1346_ = l_Bool_repr___redArg(v_v_1342_);
                v___x_1347_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1347_, 0, v___x_1345_);
                leanh::lean_ctor_set(v___x_1347_, 1, v___x_1346_);
                leanh::lean_inc(v___y_1344_);
                v___x_1348_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1348_, 0, v___y_1344_);
                leanh::lean_ctor_set(v___x_1348_, 1, v___x_1347_);
                v___x_1349_ = 0;
                v___x_1350_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1350_, 0, v___x_1348_);
                leanh::lean_ctor_set_uint8(
                    v___x_1350_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1349_,
                );
                v___x_1351_ = l_Repr_addAppParen(v___x_1350_, v_prec_1311_);
                return v___x_1351_;
            }
            6 => {
                v___x_1359_ = l_Lean_instReprDataValue_repr___closed__10;
                v___x_1360_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1361_ = l_Lean_Name_reprPrec(v_v_1356_, v___x_1360_);
                v___x_1362_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1362_, 0, v___x_1359_);
                leanh::lean_ctor_set(v___x_1362_, 1, v___x_1361_);
                leanh::lean_inc(v___y_1358_);
                v___x_1363_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1363_, 0, v___y_1358_);
                leanh::lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                v___x_1364_ = 0;
                v___x_1365_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1365_, 0, v___x_1363_);
                leanh::lean_ctor_set_uint8(
                    v___x_1365_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1364_,
                );
                v___x_1366_ = l_Repr_addAppParen(v___x_1365_, v_prec_1311_);
                return v___x_1366_;
            }
            7 => {
                v___x_1387_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1388_ = lean_nat_dec_le(v___x_1387_, v_prec_1311_);
                if v___x_1388_ == 0 {
                    v___x_1389_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1376_ = v___x_1389_;
                    state = 8;
                    continue;
                } else {
                    v___x_1390_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                        _init_l_Lean_instReprDataValue_repr___closed__4,
                    );
                    v___y_1376_ = v___x_1390_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_1377_ = l_Lean_instReprDataValue_repr___closed__13;
                v___x_1378_ = l_Nat_reprFast(v_v_1371_);
                if v_isShared_1374_ == 0 {
                    leanh::lean_ctor_set(v___x_1373_, 0, v___x_1378_);
                    v___x_1380_ = v___x_1373_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1378_);
                    v___x_1380_ = v_reuseFailAlloc_1386_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1381_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1381_, 0, v___x_1377_);
                leanh::lean_ctor_set(v___x_1381_, 1, v___x_1380_);
                leanh::lean_inc(v___y_1376_);
                v___x_1382_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1382_, 0, v___y_1376_);
                leanh::lean_ctor_set(v___x_1382_, 1, v___x_1381_);
                v___x_1383_ = 0;
                v___x_1384_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1384_, 0, v___x_1382_);
                leanh::lean_ctor_set_uint8(
                    v___x_1384_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1383_,
                );
                v___x_1385_ = l_Repr_addAppParen(v___x_1384_, v_prec_1311_);
                return v___x_1385_;
            }
            10 => {
                v___x_1411_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1412_ = lean_nat_dec_le(v___x_1411_, v_prec_1311_);
                if v___x_1412_ == 0 {
                    v___x_1413_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1397_ = v___x_1413_;
                    state = 11;
                    continue;
                } else {
                    v___x_1414_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__4_once),
                        _init_l_Lean_instReprDataValue_repr___closed__4,
                    );
                    v___y_1397_ = v___x_1414_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1398_ = l_Lean_instReprDataValue_repr___closed__16;
                v___x_1399_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17_once),
                    _init_l_Lean_instReprDataValue_repr___closed__17,
                );
                v___x_1400_ = lean_int_dec_lt(v_v_1392_, v___x_1399_);
                if v___x_1400_ == 0 {
                    v___x_1401_ = l_Int_repr(v_v_1392_);
                    leanh::lean_dec(v_v_1392_);
                    if v_isShared_1395_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1394_, 3);
                        leanh::lean_ctor_set(v___x_1394_, 0, v___x_1401_);
                        v___x_1403_ = v___x_1394_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1404_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
                        v___x_1403_ = v_reuseFailAlloc_1404_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_1405_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1406_ = l_Int_repr(v_v_1392_);
                    leanh::lean_dec(v_v_1392_);
                    if v_isShared_1395_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1394_, 3);
                        leanh::lean_ctor_set(v___x_1394_, 0, v___x_1406_);
                        v___x_1408_ = v___x_1394_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1410_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
                        v___x_1408_ = v_reuseFailAlloc_1410_;
                        state = 13;
                        continue;
                    }
                }
            }
            12 => {
                v___y_1313_ = v___y_1397_;
                v___y_1314_ = v___x_1398_;
                v___y_1315_ = v___x_1403_;
                state = 1;
                continue;
            }
            13 => {
                v___x_1409_ = l_Repr_addAppParen(v___x_1408_, v___x_1405_);
                v___y_1313_ = v___y_1397_;
                v___y_1314_ = v___x_1398_;
                v___y_1315_ = v___x_1409_;
                state = 1;
                continue;
            }
            14 => {
                v___x_1419_ = l_Lean_instReprDataValue_repr___closed__20;
                v___x_1420_ = leanh::lean_unsigned_to_nat(1024);
                v___x_1421_ = l_Lean_Syntax_instRepr_repr(v_v_1416_, v___x_1420_);
                v___x_1422_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1422_, 0, v___x_1419_);
                leanh::lean_ctor_set(v___x_1422_, 1, v___x_1421_);
                leanh::lean_inc(v___y_1418_);
                v___x_1423_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1423_, 0, v___y_1418_);
                leanh::lean_ctor_set(v___x_1423_, 1, v___x_1422_);
                v___x_1424_ = 0;
                v___x_1425_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1425_, 0, v___x_1423_);
                leanh::lean_ctor_set_uint8(
                    v___x_1425_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1424_,
                );
                v___x_1426_ = l_Repr_addAppParen(v___x_1425_, v_prec_1311_);
                return v___x_1426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instReprDataValue_repr___boxed(
    mut v_x_1431_: *mut leanh::LeanObject,
    mut v_prec_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Lean_instReprDataValue_repr(v_x_1431_, v_prec_1432_);
    leanh::lean_dec(v_prec_1432_);
    return v_res_1433_;
}
pub unsafe fn lean_data_value_beq(
    mut v_a_1436_: *mut leanh::LeanObject,
    mut v_b_1437_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1438_: u8 = 0;
    v___x_1438_ = l_Lean_instBEqDataValue_beq(v_a_1436_, v_b_1437_);
    return v___x_1438_;
}
pub unsafe fn l_Lean_DataValue_beqExp___boxed(
    mut v_a_1439_: *mut leanh::LeanObject,
    mut v_b_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = lean_data_value_beq(v_a_1439_, v_b_1440_);
    v_r_1442_ = leanh::lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn lean_mk_bool_data_value(mut v_b_1443_: u8) -> *mut leanh::LeanObject {
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1444_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_1444_, 0 as u32, v_b_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_mkBoolDataValueEx___boxed(
    mut v_b_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1446_: u8 = 0;
    let mut v_res_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1446_ = (leanh::lean_unbox(v_b_1445_) as u8);
    v_res_1447_ = lean_mk_bool_data_value(v_b_boxed_1446_);
    return v_res_1447_;
}
pub unsafe fn lean_data_value_bool(mut v_x_1448_: *mut leanh::LeanObject) -> u8 {
    if leanh::lean_obj_tag(v_x_1448_) == 1 {
        let mut v_v_1449_: u8 = 0;
        v_v_1449_ = leanh::lean_ctor_get_uint8(v_x_1448_, 0 as u32);
        leanh::lean_dec_ref_known(v_x_1448_, 0);
        return v_v_1449_;
    } else {
        let mut v___x_1450_: u8 = 0;
        leanh::lean_dec_ref(v_x_1448_);
        v___x_1450_ = 0;
        return v___x_1450_;
    }
}
pub unsafe fn l_Lean_DataValue_getBoolEx___boxed(
    mut v_x_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1452_: u8 = 0;
    let mut v_r_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1452_ = lean_data_value_bool(v_x_1451_);
    v_r_1453_ = leanh::lean_box((v_res_1452_) as usize);
    return v_r_1453_;
}
pub unsafe fn l_Lean_DataValue_sameCtor(
    mut v_x_1454_: *mut leanh::LeanObject,
    mut v_x_1455_: *mut leanh::LeanObject,
) -> u8 {
    match leanh::lean_obj_tag(v_x_1454_) {
        0 => {
            if leanh::lean_obj_tag(v_x_1455_) == 0 {
                let mut v___x_1456_: u8 = 0;
                v___x_1456_ = 1;
                return v___x_1456_;
            } else {
                let mut v___x_1457_: u8 = 0;
                v___x_1457_ = 0;
                return v___x_1457_;
            }
        }
        1 => {
            if leanh::lean_obj_tag(v_x_1455_) == 1 {
                let mut v___x_1458_: u8 = 0;
                v___x_1458_ = 1;
                return v___x_1458_;
            } else {
                let mut v___x_1459_: u8 = 0;
                v___x_1459_ = 0;
                return v___x_1459_;
            }
        }
        2 => {
            if leanh::lean_obj_tag(v_x_1455_) == 2 {
                let mut v___x_1460_: u8 = 0;
                v___x_1460_ = 1;
                return v___x_1460_;
            } else {
                let mut v___x_1461_: u8 = 0;
                v___x_1461_ = 0;
                return v___x_1461_;
            }
        }
        3 => {
            if leanh::lean_obj_tag(v_x_1455_) == 3 {
                let mut v___x_1462_: u8 = 0;
                v___x_1462_ = 1;
                return v___x_1462_;
            } else {
                let mut v___x_1463_: u8 = 0;
                v___x_1463_ = 0;
                return v___x_1463_;
            }
        }
        4 => {
            if leanh::lean_obj_tag(v_x_1455_) == 4 {
                let mut v___x_1464_: u8 = 0;
                v___x_1464_ = 1;
                return v___x_1464_;
            } else {
                let mut v___x_1465_: u8 = 0;
                v___x_1465_ = 0;
                return v___x_1465_;
            }
        }
        _ => {
            if leanh::lean_obj_tag(v_x_1455_) == 5 {
                let mut v___x_1466_: u8 = 0;
                v___x_1466_ = 1;
                return v___x_1466_;
            } else {
                let mut v___x_1467_: u8 = 0;
                v___x_1467_ = 0;
                return v___x_1467_;
            }
        }
    }
}
pub unsafe fn l_Lean_DataValue_sameCtor___boxed(
    mut v_x_1468_: *mut leanh::LeanObject,
    mut v_x_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: u8 = 0;
    let mut v_r_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_DataValue_sameCtor(v_x_1468_, v_x_1469_);
    leanh::lean_dec_ref(v_x_1469_);
    leanh::lean_dec_ref(v_x_1468_);
    v_r_1471_ = leanh::lean_box((v_res_1470_) as usize);
    return v_r_1471_;
}
pub unsafe fn lean_data_value_to_string(
    mut v_x_1474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1474_) {
        0 => {
            let mut v_v_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1475_ = leanh::lean_ctor_get(v_x_1474_, 0);
            leanh::lean_inc_ref(v_v_1475_);
            leanh::lean_dec_ref_known(v_x_1474_, 1);
            return v_v_1475_;
        }
        1 => {
            let mut v_v_1476_: u8 = 0;
            v_v_1476_ = leanh::lean_ctor_get_uint8(v_x_1474_, 0 as u32);
            leanh::lean_dec_ref_known(v_x_1474_, 0);
            if v_v_1476_ == 0 {
                let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1477_ = l_Lean_DataValue_str___closed__0;
                return v___x_1477_;
            } else {
                let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1478_ = l_Lean_DataValue_str___closed__1;
                return v___x_1478_;
            }
        }
        2 => {
            let mut v_v_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1480_: u8 = 0;
            let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1479_ = leanh::lean_ctor_get(v_x_1474_, 0);
            leanh::lean_inc(v_v_1479_);
            leanh::lean_dec_ref_known(v_x_1474_, 1);
            v___x_1480_ = 1;
            v___x_1481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_v_1479_,
                v___x_1480_,
            );
            return v___x_1481_;
        }
        3 => {
            let mut v_v_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1482_ = leanh::lean_ctor_get(v_x_1474_, 0);
            leanh::lean_inc(v_v_1482_);
            leanh::lean_dec_ref_known(v_x_1474_, 1);
            v___x_1483_ = l_Nat_reprFast(v_v_1482_);
            return v___x_1483_;
        }
        4 => {
            let mut v_v_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1484_ = leanh::lean_ctor_get(v_x_1474_, 0);
            leanh::lean_inc(v_v_1484_);
            leanh::lean_dec_ref_known(v_x_1474_, 1);
            v___x_1485_ = l_Int_repr(v_v_1484_);
            leanh::lean_dec(v_v_1484_);
            return v___x_1485_;
        }
        _ => {
            let mut v_v_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1488_: u8 = 0;
            let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1486_ = leanh::lean_ctor_get(v_x_1474_, 0);
            leanh::lean_inc(v_v_1486_);
            leanh::lean_dec_ref_known(v_x_1474_, 1);
            v___x_1487_ = leanh::lean_box(0);
            v___x_1488_ = 0;
            v___x_1489_ = l_Lean_Syntax_formatStx(v_v_1486_, v___x_1487_, v___x_1488_);
            v___x_1490_ = l_Std_Format_defWidth;
            v___x_1491_ = leanh::lean_unsigned_to_nat(0);
            v___x_1492_ = l_Std_Format_pretty(v___x_1489_, v___x_1490_, v___x_1491_, v___x_1491_);
            return v___x_1492_;
        }
    }
}
pub unsafe fn l_Lean_instCoeStringDataValue___lam__0(
    mut v_v_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1496_, 0, v_v_1495_);
    return v___x_1496_;
}
pub unsafe fn l_Lean_instCoeBoolDataValue___lam__0(
    mut v_v_1499_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_1500_, 0 as u32, v_v_1499_);
    return v___x_1500_;
}
pub unsafe fn l_Lean_instCoeBoolDataValue___lam__0___boxed(
    mut v_v_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1502_: u8 = 0;
    let mut v_res_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1502_ = (leanh::lean_unbox(v_v_1501_) as u8);
    v_res_1503_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_1502_);
    return v_res_1503_;
}
pub unsafe fn l_Lean_instCoeNameDataValue___lam__0(
    mut v_v_1506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1507_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1507_, 0, v_v_1506_);
    return v___x_1507_;
}
pub unsafe fn l_Lean_instCoeNatDataValue___lam__0(
    mut v_v_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1511_, 0, v_v_1510_);
    return v___x_1511_;
}
pub unsafe fn l_Lean_instCoeIntDataValue___lam__0(
    mut v_v_1514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1515_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1515_, 0, v_v_1514_);
    return v___x_1515_;
}
pub unsafe fn l_Lean_instCoeSyntaxDataValue___lam__0(
    mut v_v_1518_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1519_, 0, v_v_1518_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Lean_instInhabitedKVMap_default() -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = leanh::lean_box(0);
    return v___x_1522_;
}
pub unsafe fn _init_l_Lean_instInhabitedKVMap() -> *mut leanh::LeanObject {
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = leanh::lean_box(0);
    return v___x_1523_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(
    mut v_a_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1525_ = lean_nat_to_int(v_a_1524_);
    return v___x_1525_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1526_: *mut leanh::LeanObject,
    mut v_x_1527_: *mut leanh::LeanObject,
    mut v_x_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1528_) == 0 {
                    leanh::lean_dec(v_x_1526_);
                    return v_x_1527_;
                } else {
                    v_head_1529_ = leanh::lean_ctor_get(v_x_1528_, 0);
                    v_tail_1530_ = leanh::lean_ctor_get(v_x_1528_, 1);
                    v_isSharedCheck_1539_ = (!leanh::lean_is_exclusive(v_x_1528_)) as u8;
                    if v_isSharedCheck_1539_ == 0 {
                        v___x_1532_ = v_x_1528_;
                        v_isShared_1533_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1530_);
                        leanh::lean_inc(v_head_1529_);
                        leanh::lean_dec(v_x_1528_);
                        v___x_1532_ = leanh::lean_box(0);
                        v_isShared_1533_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1526_);
                if v_isShared_1533_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1532_, 5);
                    leanh::lean_ctor_set(v___x_1532_, 1, v_x_1526_);
                    leanh::lean_ctor_set(v___x_1532_, 0, v_x_1527_);
                    v___x_1535_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_x_1527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_x_1526_);
                    v___x_1535_ = v_reuseFailAlloc_1538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1536_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1536_, 0, v___x_1535_);
                leanh::lean_ctor_set(v___x_1536_, 1, v_head_1529_);
                v_x_1527_ = v___x_1536_;
                v_x_1528_ = v_tail_1530_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(
    mut v_x_1540_: *mut leanh::LeanObject,
    mut v_x_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1540_) == 0 {
        let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1541_);
        v___x_1542_ = leanh::lean_box(0);
        return v___x_1542_;
    } else {
        let mut v_tail_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1543_ = leanh::lean_ctor_get(v_x_1540_, 1);
        if leanh::lean_obj_tag(v_tail_1543_) == 0 {
            let mut v_head_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1541_);
            v_head_1544_ = leanh::lean_ctor_get(v_x_1540_, 0);
            leanh::lean_inc(v_head_1544_);
            leanh::lean_dec_ref_known(v_x_1540_, 2);
            return v_head_1544_;
        } else {
            let mut v_head_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1543_);
            v_head_1545_ = leanh::lean_ctor_get(v_x_1540_, 0);
            leanh::lean_inc(v_head_1545_);
            leanh::lean_dec_ref_known(v_x_1540_, 2);
            v___x_1546_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_1541_, v_head_1545_, v_tail_1543_);
            return v___x_1546_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0;
    v___x_1556_ = lean_string_length(v___x_1555_);
    return v___x_1556_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
    v___x_1558_ = lean_nat_to_int(v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(
    mut v_x_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1564_ = leanh::lean_ctor_get(v_x_1563_, 0);
                v_snd_1565_ = leanh::lean_ctor_get(v_x_1563_, 1);
                v_isSharedCheck_1588_ = (!leanh::lean_is_exclusive(v_x_1563_)) as u8;
                if v_isSharedCheck_1588_ == 0 {
                    v___x_1567_ = v_x_1563_;
                    v_isShared_1568_ = v_isSharedCheck_1588_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1565_);
                    leanh::lean_inc(v_fst_1564_);
                    leanh::lean_dec(v_x_1563_);
                    v___x_1567_ = leanh::lean_box(0);
                    v_isShared_1568_ = v_isSharedCheck_1588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1569_ = leanh::lean_unsigned_to_nat(0);
                v___x_1570_ = l_Lean_Name_reprPrec(v_fst_1564_, v___x_1569_);
                v___x_1571_ = leanh::lean_box(0);
                if v_isShared_1568_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1567_, 1);
                    leanh::lean_ctor_set(v___x_1567_, 1, v___x_1571_);
                    leanh::lean_ctor_set(v___x_1567_, 0, v___x_1570_);
                    v___x_1573_ = v___x_1567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1571_);
                    v___x_1573_ = v_reuseFailAlloc_1587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1574_ = l_Lean_instReprDataValue_repr(v_snd_1565_, v___x_1569_);
                v___x_1575_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                leanh::lean_ctor_set(v___x_1575_, 1, v___x_1573_);
                v___x_1576_ = l_List_reverse___redArg(v___x_1575_);
                v___x_1577_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3;
                v___x_1578_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_1576_, v___x_1577_);
                v___x_1579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
                v___x_1580_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7;
                v___x_1581_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1581_, 0, v___x_1580_);
                leanh::lean_ctor_set(v___x_1581_, 1, v___x_1578_);
                v___x_1582_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8;
                v___x_1583_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1583_, 0, v___x_1581_);
                leanh::lean_ctor_set(v___x_1583_, 1, v___x_1582_);
                v___x_1584_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1584_, 0, v___x_1579_);
                leanh::lean_ctor_set(v___x_1584_, 1, v___x_1583_);
                v___x_1585_ = 0;
                v___x_1586_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1586_, 0, v___x_1584_);
                leanh::lean_ctor_set_uint8(
                    v___x_1586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1585_,
                );
                return v___x_1586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_x_1590_: *mut leanh::LeanObject,
    mut v_x_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1591_) == 0 {
                    leanh::lean_dec(v_x_1589_);
                    return v_x_1590_;
                } else {
                    v_head_1592_ = leanh::lean_ctor_get(v_x_1591_, 0);
                    v_tail_1593_ = leanh::lean_ctor_get(v_x_1591_, 1);
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v_x_1591_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1595_ = v_x_1591_;
                        v_isShared_1596_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1593_);
                        leanh::lean_inc(v_head_1592_);
                        leanh::lean_dec(v_x_1591_);
                        v___x_1595_ = leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1589_);
                if v_isShared_1596_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1595_, 5);
                    leanh::lean_ctor_set(v___x_1595_, 1, v_x_1589_);
                    leanh::lean_ctor_set(v___x_1595_, 0, v_x_1590_);
                    v___x_1598_ = v___x_1595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_x_1590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_x_1589_);
                    v___x_1598_ = v_reuseFailAlloc_1602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1599_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1592_);
                v___x_1600_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1600_, 0, v___x_1598_);
                leanh::lean_ctor_set(v___x_1600_, 1, v___x_1599_);
                v_x_1590_ = v___x_1600_;
                v_x_1591_ = v_tail_1593_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(
    mut v_x_1604_: *mut leanh::LeanObject,
    mut v_x_1605_: *mut leanh::LeanObject,
    mut v_x_1606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1606_) == 0 {
                    leanh::lean_dec(v_x_1604_);
                    return v_x_1605_;
                } else {
                    v_head_1607_ = leanh::lean_ctor_get(v_x_1606_, 0);
                    v_tail_1608_ = leanh::lean_ctor_get(v_x_1606_, 1);
                    v_isSharedCheck_1618_ = (!leanh::lean_is_exclusive(v_x_1606_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v___x_1610_ = v_x_1606_;
                        v_isShared_1611_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1608_);
                        leanh::lean_inc(v_head_1607_);
                        leanh::lean_dec(v_x_1606_);
                        v___x_1610_ = leanh::lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_x_1604_);
                if v_isShared_1611_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1610_, 5);
                    leanh::lean_ctor_set(v___x_1610_, 1, v_x_1604_);
                    leanh::lean_ctor_set(v___x_1610_, 0, v_x_1605_);
                    v___x_1613_ = v___x_1610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_x_1605_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_x_1604_);
                    v___x_1613_ = v_reuseFailAlloc_1617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1614_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1607_);
                v___x_1615_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1615_, 0, v___x_1613_);
                leanh::lean_ctor_set(v___x_1615_, 1, v___x_1614_);
                v___x_1616_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_1604_, v___x_1615_, v_tail_1608_);
                return v___x_1616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(
    mut v_x_1619_: *mut leanh::LeanObject,
    mut v_x_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1619_) == 0 {
        let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_1620_);
        v___x_1621_ = leanh::lean_box(0);
        return v___x_1621_;
    } else {
        let mut v_tail_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_1622_ = leanh::lean_ctor_get(v_x_1619_, 1);
        if leanh::lean_obj_tag(v_tail_1622_) == 0 {
            let mut v_head_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_x_1620_);
            v_head_1623_ = leanh::lean_ctor_get(v_x_1619_, 0);
            leanh::lean_inc(v_head_1623_);
            leanh::lean_dec_ref_known(v_x_1619_, 2);
            v___x_1624_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1623_);
            return v___x_1624_;
        } else {
            let mut v_head_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_1622_);
            v_head_1625_ = leanh::lean_ctor_get(v_x_1619_, 0);
            leanh::lean_inc(v_head_1625_);
            leanh::lean_dec_ref_known(v_x_1619_, 2);
            v___x_1626_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1625_);
            v___x_1627_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_1620_, v___x_1626_, v_tail_1622_);
            return v___x_1627_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2;
    v___x_1634_ = lean_string_length(v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once
        ),
        _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4,
    );
    v___x_1636_ = lean_nat_to_int(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(
    mut v_a_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_1641_) == 0 {
        let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1642_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1;
        return v___x_1642_;
    } else {
        let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: u8 = 0;
        let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1643_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3;
        v___x_1644_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_1641_, v___x_1643_);
        v___x_1645_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(
                l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5
            ),
            core::ptr::addr_of_mut!(
                l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once
            ),
            _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5,
        );
        v___x_1646_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6;
        v___x_1647_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1647_, 0, v___x_1646_);
        leanh::lean_ctor_set(v___x_1647_, 1, v___x_1644_);
        v___x_1648_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7;
        v___x_1649_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1649_, 0, v___x_1647_);
        leanh::lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        v___x_1650_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1650_, 0, v___x_1645_);
        leanh::lean_ctor_set(v___x_1650_, 1, v___x_1649_);
        v___x_1651_ = 0;
        v___x_1652_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1652_, 0, v___x_1650_);
        leanh::lean_ctor_set_uint8(
            v___x_1652_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1651_,
        );
        return v___x_1652_;
    }
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = leanh::lean_unsigned_to_nat(11);
    v___x_1667_ = lean_nat_to_int(v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__9() -> *mut leanh::LeanObject
{
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lean_instReprKVMap_repr___redArg___closed__0;
    v___x_1670_ = lean_string_length(v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1671_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__9_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__9,
    );
    v___x_1672_ = lean_nat_to_int(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_instReprKVMap_repr___redArg(
    mut v_x_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lean_instReprKVMap_repr___redArg___closed__6;
    v___x_1679_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__7_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__7,
    );
    v___x_1680_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_1677_);
    v___x_1681_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1681_, 0, v___x_1679_);
    leanh::lean_ctor_set(v___x_1681_, 1, v___x_1680_);
    v___x_1682_ = 0;
    v___x_1683_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1683_, 0, v___x_1681_);
    leanh::lean_ctor_set_uint8(
        v___x_1683_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1682_,
    );
    v___x_1684_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1684_, 0, v___x_1678_);
    leanh::lean_ctor_set(v___x_1684_, 1, v___x_1683_);
    v___x_1685_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__10_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__10,
    );
    v___x_1686_ = l_Lean_instReprKVMap_repr___redArg___closed__11;
    v___x_1687_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1687_, 0, v___x_1686_);
    leanh::lean_ctor_set(v___x_1687_, 1, v___x_1684_);
    v___x_1688_ = l_Lean_instReprKVMap_repr___redArg___closed__12;
    v___x_1689_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1689_, 0, v___x_1687_);
    leanh::lean_ctor_set(v___x_1689_, 1, v___x_1688_);
    v___x_1690_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1690_, 0, v___x_1685_);
    leanh::lean_ctor_set(v___x_1690_, 1, v___x_1689_);
    v___x_1691_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
    leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
    leanh::lean_ctor_set_uint8(
        v___x_1691_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
        v___x_1682_,
    );
    return v___x_1691_;
}
pub unsafe fn l_Lean_instReprKVMap_repr(
    mut v_x_1692_: *mut leanh::LeanObject,
    mut v_prec_1693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Lean_instReprKVMap_repr___redArg(v_x_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Lean_instReprKVMap_repr___boxed(
    mut v_x_1695_: *mut leanh::LeanObject,
    mut v_prec_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1697_ = l_Lean_instReprKVMap_repr(v_x_1695_, v_prec_1696_);
    leanh::lean_dec(v_prec_1696_);
    return v_res_1697_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(
    mut v_a_1698_: *mut leanh::LeanObject,
    mut v_n_1699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_1698_);
    return v___x_1700_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(
    mut v_a_1701_: *mut leanh::LeanObject,
    mut v_n_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_1701_, v_n_1702_);
    leanh::lean_dec(v_n_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(
    mut v_x_1704_: *mut leanh::LeanObject,
    mut v_x_1705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1706_ =
        l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(
            v_x_1704_,
        );
    return v___x_1706_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(
    mut v_x_1707_: *mut leanh::LeanObject,
    mut v_x_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(
        v_x_1707_, v_x_1708_,
    );
    leanh::lean_dec(v_x_1708_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_KVMap_instToString___lam__0(
    mut v___f_1712_: *mut leanh::LeanObject,
    mut v_m_1713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_List_toString___redArg(v___f_1712_, v_m_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l_Lean_KVMap_empty() -> *mut leanh::LeanObject {
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1722_ = leanh::lean_box(0);
    return v___x_1722_;
}
pub unsafe fn l_Lean_KVMap_isEmpty(mut v_x_1723_: *mut leanh::LeanObject) -> u8 {
    let mut v___x_1724_: u8 = 0;
    v___x_1724_ = l_List_isEmpty___redArg(v_x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_KVMap_isEmpty___boxed(
    mut v_x_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_KVMap_isEmpty(v_x_1725_);
    leanh::lean_dec(v_x_1725_);
    v_r_1727_ = leanh::lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l_Lean_KVMap_size(
    mut v_m_1728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1729_ = l_List_lengthTR___redArg(v_m_1728_);
    return v___x_1729_;
}
pub unsafe fn l_Lean_KVMap_size___boxed(
    mut v_m_1730_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_KVMap_size(v_m_1730_);
    leanh::lean_dec(v_m_1730_);
    return v_res_1731_;
}
pub unsafe fn l_Lean_KVMap_findCore(
    mut v_x_1732_: *mut leanh::LeanObject,
    mut v_x_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1732_) == 0 {
                    v___x_1734_ = leanh::lean_box(0);
                    return v___x_1734_;
                } else {
                    v_head_1735_ = leanh::lean_ctor_get(v_x_1732_, 0);
                    v_tail_1736_ = leanh::lean_ctor_get(v_x_1732_, 1);
                    v_fst_1737_ = leanh::lean_ctor_get(v_head_1735_, 0);
                    v_snd_1738_ = leanh::lean_ctor_get(v_head_1735_, 1);
                    v___x_1739_ = lean_name_eq(v_fst_1737_, v_x_1733_);
                    if v___x_1739_ == 0 {
                        v_x_1732_ = v_tail_1736_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1738_);
                        v___x_1741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1741_, 0, v_snd_1738_);
                        return v___x_1741_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_findCore___boxed(
    mut v_x_1742_: *mut leanh::LeanObject,
    mut v_x_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Lean_KVMap_findCore(v_x_1742_, v_x_1743_);
    leanh::lean_dec(v_x_1743_);
    leanh::lean_dec(v_x_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Lean_KVMap_find(
    mut v_x_1745_: *mut leanh::LeanObject,
    mut v_x_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_KVMap_findCore(v_x_1745_, v_x_1746_);
    return v___x_1747_;
}
pub unsafe fn l_Lean_KVMap_find___boxed(
    mut v_x_1748_: *mut leanh::LeanObject,
    mut v_x_1749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_KVMap_find(v_x_1748_, v_x_1749_);
    leanh::lean_dec(v_x_1749_);
    leanh::lean_dec(v_x_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_KVMap_findD(
    mut v_m_1751_: *mut leanh::LeanObject,
    mut v_k_1752_: *mut leanh::LeanObject,
    mut v_d_u2080_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_KVMap_findCore(v_m_1751_, v_k_1752_);
    if leanh::lean_obj_tag(v___x_1754_) == 0 {
        leanh::lean_inc_ref(v_d_u2080_1753_);
        return v_d_u2080_1753_;
    } else {
        let mut v_val_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1755_ = leanh::lean_ctor_get(v___x_1754_, 0);
        leanh::lean_inc(v_val_1755_);
        leanh::lean_dec_ref_known(v___x_1754_, 1);
        return v_val_1755_;
    }
}
pub unsafe fn l_Lean_KVMap_findD___boxed(
    mut v_m_1756_: *mut leanh::LeanObject,
    mut v_k_1757_: *mut leanh::LeanObject,
    mut v_d_u2080_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lean_KVMap_findD(v_m_1756_, v_k_1757_, v_d_u2080_1758_);
    leanh::lean_dec_ref(v_d_u2080_1758_);
    leanh::lean_dec(v_k_1757_);
    leanh::lean_dec(v_m_1756_);
    return v_res_1759_;
}
pub unsafe fn l_Lean_KVMap_insertCore(
    mut v_x_1760_: *mut leanh::LeanObject,
    mut v_x_1761_: *mut leanh::LeanObject,
    mut v_x_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v_fst_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_unused_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1760_) == 0 {
                    v___x_1763_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1763_, 0, v_x_1761_);
                    leanh::lean_ctor_set(v___x_1763_, 1, v_x_1762_);
                    v___x_1764_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1764_, 0, v___x_1763_);
                    leanh::lean_ctor_set(v___x_1764_, 1, v_x_1760_);
                    return v___x_1764_;
                } else {
                    v_head_1765_ = leanh::lean_ctor_get(v_x_1760_, 0);
                    v_tail_1766_ = leanh::lean_ctor_get(v_x_1760_, 1);
                    v_isSharedCheck_1788_ = (!leanh::lean_is_exclusive(v_x_1760_)) as u8;
                    if v_isSharedCheck_1788_ == 0 {
                        v___x_1768_ = v_x_1760_;
                        v_isShared_1769_ = v_isSharedCheck_1788_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1766_);
                        leanh::lean_inc(v_head_1765_);
                        leanh::lean_dec(v_x_1760_);
                        v___x_1768_ = leanh::lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1788_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1770_ = leanh::lean_ctor_get(v_head_1765_, 0);
                v___x_1771_ = lean_name_eq(v_fst_1770_, v_x_1761_);
                if v___x_1771_ == 0 {
                    v___x_1772_ = l_Lean_KVMap_insertCore(v_tail_1766_, v_x_1761_, v_x_1762_);
                    if v_isShared_1769_ == 0 {
                        leanh::lean_ctor_set(v___x_1768_, 1, v___x_1772_);
                        v___x_1774_ = v___x_1768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_head_1765_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1772_);
                        v___x_1774_ = v_reuseFailAlloc_1775_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_fst_1770_);
                    leanh::lean_dec(v_x_1761_);
                    v_isSharedCheck_1785_ = (!leanh::lean_is_exclusive(v_head_1765_)) as u8;
                    if v_isSharedCheck_1785_ == 0 {
                        v_unused_1786_ = leanh::lean_ctor_get(v_head_1765_, 1);
                        leanh::lean_dec(v_unused_1786_);
                        v_unused_1787_ = leanh::lean_ctor_get(v_head_1765_, 0);
                        leanh::lean_dec(v_unused_1787_);
                        v___x_1777_ = v_head_1765_;
                        v_isShared_1778_ = v_isSharedCheck_1785_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_head_1765_);
                        v___x_1777_ = leanh::lean_box(0);
                        v_isShared_1778_ = v_isSharedCheck_1785_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1774_;
            }
            3 => {
                if v_isShared_1778_ == 0 {
                    leanh::lean_ctor_set(v___x_1777_, 1, v_x_1762_);
                    v___x_1780_ = v___x_1777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_fst_1770_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_x_1762_);
                    v___x_1780_ = v_reuseFailAlloc_1784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1769_ == 0 {
                    leanh::lean_ctor_set(v___x_1768_, 0, v___x_1780_);
                    v___x_1782_ = v___x_1768_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_tail_1766_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_insert(
    mut v_x_1789_: *mut leanh::LeanObject,
    mut v_x_1790_: *mut leanh::LeanObject,
    mut v_x_1791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_KVMap_insertCore(v_x_1789_, v_x_1790_, v_x_1791_);
    return v___x_1792_;
}
pub unsafe fn l_Lean_KVMap_contains(
    mut v_m_1793_: *mut leanh::LeanObject,
    mut v_n_1794_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_KVMap_findCore(v_m_1793_, v_n_1794_);
    if leanh::lean_obj_tag(v___x_1795_) == 0 {
        let mut v___x_1796_: u8 = 0;
        v___x_1796_ = 0;
        return v___x_1796_;
    } else {
        let mut v___x_1797_: u8 = 0;
        leanh::lean_dec_ref_known(v___x_1795_, 1);
        v___x_1797_ = 1;
        return v___x_1797_;
    }
}
pub unsafe fn l_Lean_KVMap_contains___boxed(
    mut v_m_1798_: *mut leanh::LeanObject,
    mut v_n_1799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1800_: u8 = 0;
    let mut v_r_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Lean_KVMap_contains(v_m_1798_, v_n_1799_);
    leanh::lean_dec(v_n_1799_);
    leanh::lean_dec(v_m_1798_);
    v_r_1801_ = leanh::lean_box((v_res_1800_) as usize);
    return v_r_1801_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(
    mut v_x_1802_: *mut leanh::LeanObject,
    mut v_a_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v_fst_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1803_) == 0 {
                    v___x_1805_ = l_List_reverse___redArg(v_a_1804_);
                    return v___x_1805_;
                } else {
                    v_head_1806_ = leanh::lean_ctor_get(v_a_1803_, 0);
                    v_tail_1807_ = leanh::lean_ctor_get(v_a_1803_, 1);
                    v_isSharedCheck_1818_ = (!leanh::lean_is_exclusive(v_a_1803_)) as u8;
                    if v_isSharedCheck_1818_ == 0 {
                        v___x_1809_ = v_a_1803_;
                        v_isShared_1810_ = v_isSharedCheck_1818_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1807_);
                        leanh::lean_inc(v_head_1806_);
                        leanh::lean_dec(v_a_1803_);
                        v___x_1809_ = leanh::lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1811_ = leanh::lean_ctor_get(v_head_1806_, 0);
                v___x_1812_ = lean_name_eq(v_fst_1811_, v_x_1802_);
                if v___x_1812_ == 0 {
                    if v_isShared_1810_ == 0 {
                        leanh::lean_ctor_set(v___x_1809_, 1, v_a_1804_);
                        v___x_1814_ = v___x_1809_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1816_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_head_1806_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1804_);
                        v___x_1814_ = v_reuseFailAlloc_1816_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1809_);
                    leanh::lean_dec(v_head_1806_);
                    v_a_1803_ = v_tail_1807_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_a_1803_ = v_tail_1807_;
                v_a_1804_ = v___x_1814_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0___boxed(
    mut v_x_1819_: *mut leanh::LeanObject,
    mut v_a_1820_: *mut leanh::LeanObject,
    mut v_a_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1822_ =
        l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_1819_, v_a_1820_, v_a_1821_);
    leanh::lean_dec(v_x_1819_);
    return v_res_1822_;
}
pub unsafe fn l_Lean_KVMap_erase(
    mut v_x_1823_: *mut leanh::LeanObject,
    mut v_x_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1825_ = leanh::lean_box(0);
    v___x_1826_ =
        l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_1824_, v_x_1823_, v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn l_Lean_KVMap_erase___boxed(
    mut v_x_1827_: *mut leanh::LeanObject,
    mut v_x_1828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lean_KVMap_erase(v_x_1827_, v_x_1828_);
    leanh::lean_dec(v_x_1828_);
    return v_res_1829_;
}
pub unsafe fn l_Lean_KVMap_getString(
    mut v_m_1830_: *mut leanh::LeanObject,
    mut v_k_1831_: *mut leanh::LeanObject,
    mut v_defVal_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Lean_KVMap_findCore(v_m_1830_, v_k_1831_);
    if leanh::lean_obj_tag(v___x_1833_) == 1 {
        let mut v_val_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1834_ = leanh::lean_ctor_get(v___x_1833_, 0);
        leanh::lean_inc(v_val_1834_);
        leanh::lean_dec_ref_known(v___x_1833_, 1);
        if leanh::lean_obj_tag(v_val_1834_) == 0 {
            let mut v_v_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1835_ = leanh::lean_ctor_get(v_val_1834_, 0);
            leanh::lean_inc_ref(v_v_1835_);
            leanh::lean_dec_ref_known(v_val_1834_, 1);
            return v_v_1835_;
        } else {
            leanh::lean_dec(v_val_1834_);
            leanh::lean_inc_ref(v_defVal_1832_);
            return v_defVal_1832_;
        }
    } else {
        leanh::lean_dec(v___x_1833_);
        leanh::lean_inc_ref(v_defVal_1832_);
        return v_defVal_1832_;
    }
}
pub unsafe fn l_Lean_KVMap_getString___boxed(
    mut v_m_1836_: *mut leanh::LeanObject,
    mut v_k_1837_: *mut leanh::LeanObject,
    mut v_defVal_1838_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_KVMap_getString(v_m_1836_, v_k_1837_, v_defVal_1838_);
    leanh::lean_dec_ref(v_defVal_1838_);
    leanh::lean_dec(v_k_1837_);
    leanh::lean_dec(v_m_1836_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_KVMap_getNat(
    mut v_m_1840_: *mut leanh::LeanObject,
    mut v_k_1841_: *mut leanh::LeanObject,
    mut v_defVal_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lean_KVMap_findCore(v_m_1840_, v_k_1841_);
    if leanh::lean_obj_tag(v___x_1843_) == 1 {
        let mut v_val_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1844_ = leanh::lean_ctor_get(v___x_1843_, 0);
        leanh::lean_inc(v_val_1844_);
        leanh::lean_dec_ref_known(v___x_1843_, 1);
        if leanh::lean_obj_tag(v_val_1844_) == 3 {
            let mut v_v_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1845_ = leanh::lean_ctor_get(v_val_1844_, 0);
            leanh::lean_inc(v_v_1845_);
            leanh::lean_dec_ref_known(v_val_1844_, 1);
            return v_v_1845_;
        } else {
            leanh::lean_dec(v_val_1844_);
            leanh::lean_inc(v_defVal_1842_);
            return v_defVal_1842_;
        }
    } else {
        leanh::lean_dec(v___x_1843_);
        leanh::lean_inc(v_defVal_1842_);
        return v_defVal_1842_;
    }
}
pub unsafe fn l_Lean_KVMap_getNat___boxed(
    mut v_m_1846_: *mut leanh::LeanObject,
    mut v_k_1847_: *mut leanh::LeanObject,
    mut v_defVal_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_KVMap_getNat(v_m_1846_, v_k_1847_, v_defVal_1848_);
    leanh::lean_dec(v_defVal_1848_);
    leanh::lean_dec(v_k_1847_);
    leanh::lean_dec(v_m_1846_);
    return v_res_1849_;
}
pub unsafe fn l_Lean_KVMap_getInt(
    mut v_m_1850_: *mut leanh::LeanObject,
    mut v_k_1851_: *mut leanh::LeanObject,
    mut v_defVal_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_KVMap_findCore(v_m_1850_, v_k_1851_);
    if leanh::lean_obj_tag(v___x_1853_) == 1 {
        let mut v_val_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1854_ = leanh::lean_ctor_get(v___x_1853_, 0);
        leanh::lean_inc(v_val_1854_);
        leanh::lean_dec_ref_known(v___x_1853_, 1);
        if leanh::lean_obj_tag(v_val_1854_) == 4 {
            let mut v_v_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1855_ = leanh::lean_ctor_get(v_val_1854_, 0);
            leanh::lean_inc(v_v_1855_);
            leanh::lean_dec_ref_known(v_val_1854_, 1);
            return v_v_1855_;
        } else {
            leanh::lean_dec(v_val_1854_);
            leanh::lean_inc(v_defVal_1852_);
            return v_defVal_1852_;
        }
    } else {
        leanh::lean_dec(v___x_1853_);
        leanh::lean_inc(v_defVal_1852_);
        return v_defVal_1852_;
    }
}
pub unsafe fn l_Lean_KVMap_getInt___boxed(
    mut v_m_1856_: *mut leanh::LeanObject,
    mut v_k_1857_: *mut leanh::LeanObject,
    mut v_defVal_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lean_KVMap_getInt(v_m_1856_, v_k_1857_, v_defVal_1858_);
    leanh::lean_dec(v_defVal_1858_);
    leanh::lean_dec(v_k_1857_);
    leanh::lean_dec(v_m_1856_);
    return v_res_1859_;
}
pub unsafe fn l_Lean_KVMap_getBool(
    mut v_m_1860_: *mut leanh::LeanObject,
    mut v_k_1861_: *mut leanh::LeanObject,
    mut v_defVal_1862_: u8,
) -> u8 {
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Lean_KVMap_findCore(v_m_1860_, v_k_1861_);
    if leanh::lean_obj_tag(v___x_1863_) == 1 {
        let mut v_val_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1864_ = leanh::lean_ctor_get(v___x_1863_, 0);
        leanh::lean_inc(v_val_1864_);
        leanh::lean_dec_ref_known(v___x_1863_, 1);
        if leanh::lean_obj_tag(v_val_1864_) == 1 {
            let mut v_v_1865_: u8 = 0;
            v_v_1865_ = leanh::lean_ctor_get_uint8(v_val_1864_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1864_, 0);
            return v_v_1865_;
        } else {
            leanh::lean_dec(v_val_1864_);
            return v_defVal_1862_;
        }
    } else {
        leanh::lean_dec(v___x_1863_);
        return v_defVal_1862_;
    }
}
pub unsafe fn l_Lean_KVMap_getBool___boxed(
    mut v_m_1866_: *mut leanh::LeanObject,
    mut v_k_1867_: *mut leanh::LeanObject,
    mut v_defVal_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_defVal_boxed_1869_: u8 = 0;
    let mut v_res_1870_: u8 = 0;
    let mut v_r_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_defVal_boxed_1869_ = (leanh::lean_unbox(v_defVal_1868_) as u8);
    v_res_1870_ = l_Lean_KVMap_getBool(v_m_1866_, v_k_1867_, v_defVal_boxed_1869_);
    leanh::lean_dec(v_k_1867_);
    leanh::lean_dec(v_m_1866_);
    v_r_1871_ = leanh::lean_box((v_res_1870_) as usize);
    return v_r_1871_;
}
pub unsafe fn l_Lean_KVMap_getName(
    mut v_m_1872_: *mut leanh::LeanObject,
    mut v_k_1873_: *mut leanh::LeanObject,
    mut v_defVal_1874_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_KVMap_findCore(v_m_1872_, v_k_1873_);
    if leanh::lean_obj_tag(v___x_1875_) == 1 {
        let mut v_val_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1876_ = leanh::lean_ctor_get(v___x_1875_, 0);
        leanh::lean_inc(v_val_1876_);
        leanh::lean_dec_ref_known(v___x_1875_, 1);
        if leanh::lean_obj_tag(v_val_1876_) == 2 {
            let mut v_v_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1877_ = leanh::lean_ctor_get(v_val_1876_, 0);
            leanh::lean_inc(v_v_1877_);
            leanh::lean_dec_ref_known(v_val_1876_, 1);
            return v_v_1877_;
        } else {
            leanh::lean_dec(v_val_1876_);
            leanh::lean_inc(v_defVal_1874_);
            return v_defVal_1874_;
        }
    } else {
        leanh::lean_dec(v___x_1875_);
        leanh::lean_inc(v_defVal_1874_);
        return v_defVal_1874_;
    }
}
pub unsafe fn l_Lean_KVMap_getName___boxed(
    mut v_m_1878_: *mut leanh::LeanObject,
    mut v_k_1879_: *mut leanh::LeanObject,
    mut v_defVal_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_Lean_KVMap_getName(v_m_1878_, v_k_1879_, v_defVal_1880_);
    leanh::lean_dec(v_defVal_1880_);
    leanh::lean_dec(v_k_1879_);
    leanh::lean_dec(v_m_1878_);
    return v_res_1881_;
}
pub unsafe fn l_Lean_KVMap_getSyntax(
    mut v_m_1882_: *mut leanh::LeanObject,
    mut v_k_1883_: *mut leanh::LeanObject,
    mut v_defVal_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_KVMap_findCore(v_m_1882_, v_k_1883_);
    if leanh::lean_obj_tag(v___x_1885_) == 1 {
        let mut v_val_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1886_ = leanh::lean_ctor_get(v___x_1885_, 0);
        leanh::lean_inc(v_val_1886_);
        leanh::lean_dec_ref_known(v___x_1885_, 1);
        if leanh::lean_obj_tag(v_val_1886_) == 5 {
            let mut v_v_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_1887_ = leanh::lean_ctor_get(v_val_1886_, 0);
            leanh::lean_inc(v_v_1887_);
            leanh::lean_dec_ref_known(v_val_1886_, 1);
            return v_v_1887_;
        } else {
            leanh::lean_dec(v_val_1886_);
            leanh::lean_inc(v_defVal_1884_);
            return v_defVal_1884_;
        }
    } else {
        leanh::lean_dec(v___x_1885_);
        leanh::lean_inc(v_defVal_1884_);
        return v_defVal_1884_;
    }
}
pub unsafe fn l_Lean_KVMap_getSyntax___boxed(
    mut v_m_1888_: *mut leanh::LeanObject,
    mut v_k_1889_: *mut leanh::LeanObject,
    mut v_defVal_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_KVMap_getSyntax(v_m_1888_, v_k_1889_, v_defVal_1890_);
    leanh::lean_dec(v_defVal_1890_);
    leanh::lean_dec(v_k_1889_);
    leanh::lean_dec(v_m_1888_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_KVMap_setString(
    mut v_m_1892_: *mut leanh::LeanObject,
    mut v_k_1893_: *mut leanh::LeanObject,
    mut v_v_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1895_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1895_, 0, v_v_1894_);
    v___x_1896_ = l_Lean_KVMap_insertCore(v_m_1892_, v_k_1893_, v___x_1895_);
    return v___x_1896_;
}
pub unsafe fn l_Lean_KVMap_setNat(
    mut v_m_1897_: *mut leanh::LeanObject,
    mut v_k_1898_: *mut leanh::LeanObject,
    mut v_v_1899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1900_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1900_, 0, v_v_1899_);
    v___x_1901_ = l_Lean_KVMap_insertCore(v_m_1897_, v_k_1898_, v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_KVMap_setInt(
    mut v_m_1902_: *mut leanh::LeanObject,
    mut v_k_1903_: *mut leanh::LeanObject,
    mut v_v_1904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1905_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1905_, 0, v_v_1904_);
    v___x_1906_ = l_Lean_KVMap_insertCore(v_m_1902_, v_k_1903_, v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_KVMap_setBool(
    mut v_m_1907_: *mut leanh::LeanObject,
    mut v_k_1908_: *mut leanh::LeanObject,
    mut v_v_1909_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1910_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    leanh::lean_ctor_set_uint8(v___x_1910_, 0 as u32, v_v_1909_);
    v___x_1911_ = l_Lean_KVMap_insertCore(v_m_1907_, v_k_1908_, v___x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_KVMap_setBool___boxed(
    mut v_m_1912_: *mut leanh::LeanObject,
    mut v_k_1913_: *mut leanh::LeanObject,
    mut v_v_1914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_1915_: u8 = 0;
    let mut v_res_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_1915_ = (leanh::lean_unbox(v_v_1914_) as u8);
    v_res_1916_ = l_Lean_KVMap_setBool(v_m_1912_, v_k_1913_, v_v_boxed_1915_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_KVMap_setName(
    mut v_m_1917_: *mut leanh::LeanObject,
    mut v_k_1918_: *mut leanh::LeanObject,
    mut v_v_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1920_, 0, v_v_1919_);
    v___x_1921_ = l_Lean_KVMap_insertCore(v_m_1917_, v_k_1918_, v___x_1920_);
    return v___x_1921_;
}
pub unsafe fn l_Lean_KVMap_setSyntax(
    mut v_m_1922_: *mut leanh::LeanObject,
    mut v_k_1923_: *mut leanh::LeanObject,
    mut v_v_1924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1925_, 0, v_v_1924_);
    v___x_1926_ = l_Lean_KVMap_insertCore(v_m_1922_, v_k_1923_, v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Lean_KVMap_updateString(
    mut v_m_1927_: *mut leanh::LeanObject,
    mut v_k_1928_: *mut leanh::LeanObject,
    mut v_f_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lean_instInhabitedDataValue_default___closed__0;
    v___x_1931_ = l_Lean_KVMap_getString(v_m_1927_, v_k_1928_, v___x_1930_);
    v___x_1932_ = leanh::lean_apply_1(v_f_1929_, v___x_1931_);
    v___x_1933_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1933_, 0, v___x_1932_);
    v___x_1934_ = l_Lean_KVMap_insertCore(v_m_1927_, v_k_1928_, v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_KVMap_updateNat(
    mut v_m_1935_: *mut leanh::LeanObject,
    mut v_k_1936_: *mut leanh::LeanObject,
    mut v_f_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = leanh::lean_unsigned_to_nat(0);
    v___x_1939_ = l_Lean_KVMap_getNat(v_m_1935_, v_k_1936_, v___x_1938_);
    v___x_1940_ = leanh::lean_apply_1(v_f_1937_, v___x_1939_);
    v___x_1941_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1941_, 0, v___x_1940_);
    v___x_1942_ = l_Lean_KVMap_insertCore(v_m_1935_, v_k_1936_, v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn l_Lean_KVMap_updateInt(
    mut v_m_1943_: *mut leanh::LeanObject,
    mut v_k_1944_: *mut leanh::LeanObject,
    mut v_f_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17_once),
        _init_l_Lean_instReprDataValue_repr___closed__17,
    );
    v___x_1947_ = l_Lean_KVMap_getInt(v_m_1943_, v_k_1944_, v___x_1946_);
    v___x_1948_ = leanh::lean_apply_1(v_f_1945_, v___x_1947_);
    v___x_1949_ = leanh::lean_alloc_ctor(4, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1949_, 0, v___x_1948_);
    v___x_1950_ = l_Lean_KVMap_insertCore(v_m_1943_, v_k_1944_, v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_KVMap_updateBool(
    mut v_m_1951_: *mut leanh::LeanObject,
    mut v_k_1952_: *mut leanh::LeanObject,
    mut v_f_1953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1954_ = 0;
    v___x_1955_ = l_Lean_KVMap_getBool(v_m_1951_, v_k_1952_, v___x_1954_);
    v___x_1956_ = leanh::lean_box((v___x_1955_) as usize);
    v___x_1957_ = leanh::lean_apply_1(v_f_1953_, v___x_1956_);
    v___x_1958_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
    v___x_1959_ = (leanh::lean_unbox(v___x_1957_) as u8);
    leanh::lean_ctor_set_uint8(v___x_1958_, 0 as u32, v___x_1959_);
    v___x_1960_ = l_Lean_KVMap_insertCore(v_m_1951_, v_k_1952_, v___x_1958_);
    return v___x_1960_;
}
pub unsafe fn l_Lean_KVMap_updateName(
    mut v_m_1961_: *mut leanh::LeanObject,
    mut v_k_1962_: *mut leanh::LeanObject,
    mut v_f_1963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = leanh::lean_box(0);
    v___x_1965_ = l_Lean_KVMap_getName(v_m_1961_, v_k_1962_, v___x_1964_);
    v___x_1966_ = leanh::lean_apply_1(v_f_1963_, v___x_1965_);
    v___x_1967_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    v___x_1968_ = l_Lean_KVMap_insertCore(v_m_1961_, v_k_1962_, v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_KVMap_updateSyntax(
    mut v_m_1969_: *mut leanh::LeanObject,
    mut v_k_1970_: *mut leanh::LeanObject,
    mut v_f_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = leanh::lean_box(0);
    v___x_1973_ = l_Lean_KVMap_getSyntax(v_m_1969_, v_k_1970_, v___x_1972_);
    v___x_1974_ = leanh::lean_apply_1(v_f_1971_, v___x_1973_);
    v___x_1975_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1975_, 0, v___x_1974_);
    v___x_1976_ = l_Lean_KVMap_insertCore(v_m_1969_, v_k_1970_, v___x_1975_);
    return v___x_1976_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg___lam__0(
    mut v_f_1977_: *mut leanh::LeanObject,
    mut v_a_1978_: *mut leanh::LeanObject,
    mut v_x_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1981_ = leanh::lean_apply_2(v_f_1977_, v_a_1978_, v___y_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg(
    mut v_inst_1982_: *mut leanh::LeanObject,
    mut v_kv_1983_: *mut leanh::LeanObject,
    mut v_init_1984_: *mut leanh::LeanObject,
    mut v_f_1985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1986_ = leanh::lean_alloc_closure(
        l_Lean_KVMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1986_, 0, v_f_1985_);
    v___x_1987_ =
        l_List_forIn_x27_loop___redArg(v_inst_1982_, v___f_1986_, v_kv_1983_, v_init_1984_);
    return v___x_1987_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg___boxed(
    mut v_inst_1988_: *mut leanh::LeanObject,
    mut v_kv_1989_: *mut leanh::LeanObject,
    mut v_init_1990_: *mut leanh::LeanObject,
    mut v_f_1991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_KVMap_forIn___redArg(v_inst_1988_, v_kv_1989_, v_init_1990_, v_f_1991_);
    leanh::lean_dec(v_kv_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Lean_KVMap_forIn(
    mut v_00_u03b4_1993_: *mut leanh::LeanObject,
    mut v_m_1994_: *mut leanh::LeanObject,
    mut v_inst_1995_: *mut leanh::LeanObject,
    mut v_kv_1996_: *mut leanh::LeanObject,
    mut v_init_1997_: *mut leanh::LeanObject,
    mut v_f_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1999_ = leanh::lean_alloc_closure(
        l_Lean_KVMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_1999_, 0, v_f_1998_);
    v___x_2000_ =
        l_List_forIn_x27_loop___redArg(v_inst_1995_, v___f_1999_, v_kv_1996_, v_init_1997_);
    return v___x_2000_;
}
pub unsafe fn l_Lean_KVMap_forIn___boxed(
    mut v_00_u03b4_2001_: *mut leanh::LeanObject,
    mut v_m_2002_: *mut leanh::LeanObject,
    mut v_inst_2003_: *mut leanh::LeanObject,
    mut v_kv_2004_: *mut leanh::LeanObject,
    mut v_init_2005_: *mut leanh::LeanObject,
    mut v_f_2006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_KVMap_forIn(
        v_00_u03b4_2001_,
        v_m_2002_,
        v_inst_2003_,
        v_kv_2004_,
        v_init_2005_,
        v_f_2006_,
    );
    leanh::lean_dec(v_kv_2004_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v_a_2009_: *mut leanh::LeanObject,
    mut v_x_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = leanh::lean_apply_2(v___y_2008_, v_a_2009_, v___y_2011_);
    return v___x_2012_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(
    mut v_inst_2013_: *mut leanh::LeanObject,
    mut v_00_u03b2_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2018_ = leanh::lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2018_, 0, v___y_2017_);
    v___x_2019_ =
        l_List_forIn_x27_loop___redArg(v_inst_2013_, v___f_2018_, v___y_2015_, v___y_2016_);
    return v___x_2019_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed(
    mut v_inst_2020_: *mut leanh::LeanObject,
    mut v_00_u03b2_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(
        v_inst_2020_,
        v_00_u03b2_2021_,
        v___y_2022_,
        v___y_2023_,
        v___y_2024_,
    );
    leanh::lean_dec(v___y_2022_);
    return v_res_2025_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(
    mut v_inst_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2027_ = leanh::lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2027_, 0, v_inst_2026_);
    return v___f_2027_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad(
    mut v_m_2028_: *mut leanh::LeanObject,
    mut v_inst_2029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2030_ = leanh::lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_2030_, 0, v_inst_2029_);
    return v___f_2030_;
}
pub unsafe fn l_Lean_KVMap_subsetAux(
    mut v_x_2031_: *mut leanh::LeanObject,
    mut v_x_2032_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2033_: u8 = 0;
    let mut v_head_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v_val_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2031_) == 0 {
                    v___x_2033_ = 1;
                    return v___x_2033_;
                } else {
                    v_head_2034_ = leanh::lean_ctor_get(v_x_2031_, 0);
                    leanh::lean_inc(v_head_2034_);
                    v_tail_2035_ = leanh::lean_ctor_get(v_x_2031_, 1);
                    leanh::lean_inc(v_tail_2035_);
                    leanh::lean_dec_ref_known(v_x_2031_, 2);
                    v_fst_2036_ = leanh::lean_ctor_get(v_head_2034_, 0);
                    leanh::lean_inc(v_fst_2036_);
                    v_snd_2037_ = leanh::lean_ctor_get(v_head_2034_, 1);
                    leanh::lean_inc(v_snd_2037_);
                    leanh::lean_dec(v_head_2034_);
                    v___x_2038_ = l_Lean_KVMap_findCore(v_x_2032_, v_fst_2036_);
                    leanh::lean_dec(v_fst_2036_);
                    if leanh::lean_obj_tag(v___x_2038_) == 0 {
                        leanh::lean_dec(v_snd_2037_);
                        leanh::lean_dec(v_tail_2035_);
                        v___x_2039_ = 0;
                        return v___x_2039_;
                    } else {
                        v_val_2040_ = leanh::lean_ctor_get(v___x_2038_, 0);
                        leanh::lean_inc(v_val_2040_);
                        leanh::lean_dec_ref_known(v___x_2038_, 1);
                        v___x_2041_ = l_Lean_instBEqDataValue_beq(v_snd_2037_, v_val_2040_);
                        if v___x_2041_ == 0 {
                            leanh::lean_dec(v_tail_2035_);
                            return v___x_2041_;
                        } else {
                            v_x_2031_ = v_tail_2035_;
                            state = 0;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_subsetAux___boxed(
    mut v_x_2043_: *mut leanh::LeanObject,
    mut v_x_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2045_: u8 = 0;
    let mut v_r_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2045_ = l_Lean_KVMap_subsetAux(v_x_2043_, v_x_2044_);
    leanh::lean_dec(v_x_2044_);
    v_r_2046_ = leanh::lean_box((v_res_2045_) as usize);
    return v_r_2046_;
}
pub unsafe fn l_Lean_KVMap_subset(
    mut v_x_2047_: *mut leanh::LeanObject,
    mut v_x_2048_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2049_: u8 = 0;
    v___x_2049_ = l_Lean_KVMap_subsetAux(v_x_2047_, v_x_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Lean_KVMap_subset___boxed(
    mut v_x_2050_: *mut leanh::LeanObject,
    mut v_x_2051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2052_: u8 = 0;
    let mut v_r_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2052_ = l_Lean_KVMap_subset(v_x_2050_, v_x_2051_);
    leanh::lean_dec(v_x_2051_);
    v_r_2053_ = leanh::lean_box((v_res_2052_) as usize);
    return v_r_2053_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
    mut v_mergeFn_2054_: *mut leanh::LeanObject,
    mut v_as_x27_2055_: *mut leanh::LeanObject,
    mut v_b_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_2055_) == 0 {
                    leanh::lean_dec_ref(v_mergeFn_2054_);
                    return v_b_2056_;
                } else {
                    v_head_2057_ = leanh::lean_ctor_get(v_as_x27_2055_, 0);
                    v_tail_2058_ = leanh::lean_ctor_get(v_as_x27_2055_, 1);
                    v_fst_2059_ = leanh::lean_ctor_get(v_head_2057_, 0);
                    v_snd_2060_ = leanh::lean_ctor_get(v_head_2057_, 1);
                    v___x_2061_ = l_Lean_KVMap_findCore(v_b_2056_, v_fst_2059_);
                    if leanh::lean_obj_tag(v___x_2061_) == 1 {
                        v_val_2062_ = leanh::lean_ctor_get(v___x_2061_, 0);
                        leanh::lean_inc(v_val_2062_);
                        leanh::lean_dec_ref_known(v___x_2061_, 1);
                        leanh::lean_inc_ref(v_mergeFn_2054_);
                        leanh::lean_inc(v_snd_2060_);
                        leanh::lean_inc_n(v_fst_2059_, 2);
                        v___x_2063_ = leanh::lean_apply_3(
                            v_mergeFn_2054_,
                            v_fst_2059_,
                            v_val_2062_,
                            v_snd_2060_,
                        );
                        v___x_2064_ = l_Lean_KVMap_insertCore(v_b_2056_, v_fst_2059_, v___x_2063_);
                        v_as_x27_2055_ = v_tail_2058_;
                        v_b_2056_ = v___x_2064_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_2061_);
                        leanh::lean_inc(v_snd_2060_);
                        leanh::lean_inc(v_fst_2059_);
                        v___x_2066_ = l_Lean_KVMap_insertCore(v_b_2056_, v_fst_2059_, v_snd_2060_);
                        v_as_x27_2055_ = v_tail_2058_;
                        v_b_2056_ = v___x_2066_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg___boxed(
    mut v_mergeFn_2068_: *mut leanh::LeanObject,
    mut v_as_x27_2069_: *mut leanh::LeanObject,
    mut v_b_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2068_,
        v_as_x27_2069_,
        v_b_2070_,
    );
    leanh::lean_dec(v_as_x27_2069_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_KVMap_mergeBy(
    mut v_mergeFn_2072_: *mut leanh::LeanObject,
    mut v_l_2073_: *mut leanh::LeanObject,
    mut v_r_2074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2072_,
        v_r_2074_,
        v_l_2073_,
    );
    return v___x_2075_;
}
pub unsafe fn l_Lean_KVMap_mergeBy___boxed(
    mut v_mergeFn_2076_: *mut leanh::LeanObject,
    mut v_l_2077_: *mut leanh::LeanObject,
    mut v_r_2078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_KVMap_mergeBy(v_mergeFn_2076_, v_l_2077_, v_r_2078_);
    leanh::lean_dec(v_r_2078_);
    return v_res_2079_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(
    mut v_mergeFn_2080_: *mut leanh::LeanObject,
    mut v_as_2081_: *mut leanh::LeanObject,
    mut v_as_x27_2082_: *mut leanh::LeanObject,
    mut v_b_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2080_,
        v_as_x27_2082_,
        v_b_2083_,
    );
    return v___x_2085_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(
    mut v_mergeFn_2086_: *mut leanh::LeanObject,
    mut v_as_2087_: *mut leanh::LeanObject,
    mut v_as_x27_2088_: *mut leanh::LeanObject,
    mut v_b_2089_: *mut leanh::LeanObject,
    mut v_a_2090_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(
        v_mergeFn_2086_,
        v_as_2087_,
        v_as_x27_2088_,
        v_b_2089_,
        v_a_2090_,
    );
    leanh::lean_dec(v_as_x27_2088_);
    leanh::lean_dec(v_as_2087_);
    return v_res_2091_;
}
pub unsafe fn l_Lean_KVMap_eqv(
    mut v_m_u2081_2092_: *mut leanh::LeanObject,
    mut v_m_u2082_2093_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2094_: u8 = 0;
    leanh::lean_inc(v_m_u2081_2092_);
    v___x_2094_ = l_Lean_KVMap_subsetAux(v_m_u2081_2092_, v_m_u2082_2093_);
    if v___x_2094_ == 0 {
        leanh::lean_dec(v_m_u2082_2093_);
        leanh::lean_dec(v_m_u2081_2092_);
        return v___x_2094_;
    } else {
        let mut v___x_2095_: u8 = 0;
        v___x_2095_ = l_Lean_KVMap_subsetAux(v_m_u2082_2093_, v_m_u2081_2092_);
        leanh::lean_dec(v_m_u2081_2092_);
        return v___x_2095_;
    }
}
pub unsafe fn l_Lean_KVMap_eqv___boxed(
    mut v_m_u2081_2096_: *mut leanh::LeanObject,
    mut v_m_u2082_2097_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2098_: u8 = 0;
    let mut v_r_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_KVMap_eqv(v_m_u2081_2096_, v_m_u2082_2097_);
    v_r_2099_ = leanh::lean_box((v_res_2098_) as usize);
    return v_r_2099_;
}
pub unsafe fn l_Lean_KVMap_get_x3f___redArg(
    mut v_inst_2102_: *mut leanh::LeanObject,
    mut v_m_2103_: *mut leanh::LeanObject,
    mut v_k_2104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ofDataValue_x3f_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2105_ = leanh::lean_ctor_get(v_inst_2102_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2105_);
    leanh::lean_dec_ref(v_inst_2102_);
    v___x_2106_ = l_Lean_KVMap_findCore(v_m_2103_, v_k_2104_);
    if leanh::lean_obj_tag(v___x_2106_) == 0 {
        let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ofDataValue_x3f_2105_);
        v___x_2107_ = leanh::lean_box(0);
        return v___x_2107_;
    } else {
        let mut v_val_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2108_ = leanh::lean_ctor_get(v___x_2106_, 0);
        leanh::lean_inc(v_val_2108_);
        leanh::lean_dec_ref_known(v___x_2106_, 1);
        v___x_2109_ = leanh::lean_apply_1(v_ofDataValue_x3f_2105_, v_val_2108_);
        return v___x_2109_;
    }
}
pub unsafe fn l_Lean_KVMap_get_x3f___redArg___boxed(
    mut v_inst_2110_: *mut leanh::LeanObject,
    mut v_m_2111_: *mut leanh::LeanObject,
    mut v_k_2112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2113_ = l_Lean_KVMap_get_x3f___redArg(v_inst_2110_, v_m_2111_, v_k_2112_);
    leanh::lean_dec(v_k_2112_);
    leanh::lean_dec(v_m_2111_);
    return v_res_2113_;
}
pub unsafe fn l_Lean_KVMap_get_x3f(
    mut v_00_u03b1_2114_: *mut leanh::LeanObject,
    mut v_inst_2115_: *mut leanh::LeanObject,
    mut v_m_2116_: *mut leanh::LeanObject,
    mut v_k_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ofDataValue_x3f_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2118_ = leanh::lean_ctor_get(v_inst_2115_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2118_);
    leanh::lean_dec_ref(v_inst_2115_);
    v___x_2119_ = l_Lean_KVMap_findCore(v_m_2116_, v_k_2117_);
    if leanh::lean_obj_tag(v___x_2119_) == 0 {
        let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_ofDataValue_x3f_2118_);
        v___x_2120_ = leanh::lean_box(0);
        return v___x_2120_;
    } else {
        let mut v_val_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2121_ = leanh::lean_ctor_get(v___x_2119_, 0);
        leanh::lean_inc(v_val_2121_);
        leanh::lean_dec_ref_known(v___x_2119_, 1);
        v___x_2122_ = leanh::lean_apply_1(v_ofDataValue_x3f_2118_, v_val_2121_);
        return v___x_2122_;
    }
}
pub unsafe fn l_Lean_KVMap_get_x3f___boxed(
    mut v_00_u03b1_2123_: *mut leanh::LeanObject,
    mut v_inst_2124_: *mut leanh::LeanObject,
    mut v_m_2125_: *mut leanh::LeanObject,
    mut v_k_2126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lean_KVMap_get_x3f(v_00_u03b1_2123_, v_inst_2124_, v_m_2125_, v_k_2126_);
    leanh::lean_dec(v_k_2126_);
    leanh::lean_dec(v_m_2125_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_KVMap_get___redArg(
    mut v_inst_2128_: *mut leanh::LeanObject,
    mut v_m_2129_: *mut leanh::LeanObject,
    mut v_k_2130_: *mut leanh::LeanObject,
    mut v_defVal_2131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ofDataValue_x3f_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2132_ = leanh::lean_ctor_get(v_inst_2128_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2132_);
    leanh::lean_dec_ref(v_inst_2128_);
    v___x_2133_ = l_Lean_KVMap_findCore(v_m_2129_, v_k_2130_);
    if leanh::lean_obj_tag(v___x_2133_) == 0 {
        leanh::lean_dec_ref(v_ofDataValue_x3f_2132_);
        leanh::lean_inc(v_defVal_2131_);
        return v_defVal_2131_;
    } else {
        let mut v_val_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2134_ = leanh::lean_ctor_get(v___x_2133_, 0);
        leanh::lean_inc(v_val_2134_);
        leanh::lean_dec_ref_known(v___x_2133_, 1);
        v___x_2135_ = leanh::lean_apply_1(v_ofDataValue_x3f_2132_, v_val_2134_);
        if leanh::lean_obj_tag(v___x_2135_) == 0 {
            leanh::lean_inc(v_defVal_2131_);
            return v_defVal_2131_;
        } else {
            let mut v_val_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2136_ = leanh::lean_ctor_get(v___x_2135_, 0);
            leanh::lean_inc(v_val_2136_);
            leanh::lean_dec_ref_known(v___x_2135_, 1);
            return v_val_2136_;
        }
    }
}
pub unsafe fn l_Lean_KVMap_get___redArg___boxed(
    mut v_inst_2137_: *mut leanh::LeanObject,
    mut v_m_2138_: *mut leanh::LeanObject,
    mut v_k_2139_: *mut leanh::LeanObject,
    mut v_defVal_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lean_KVMap_get___redArg(v_inst_2137_, v_m_2138_, v_k_2139_, v_defVal_2140_);
    leanh::lean_dec(v_defVal_2140_);
    leanh::lean_dec(v_k_2139_);
    leanh::lean_dec(v_m_2138_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_KVMap_get(
    mut v_00_u03b1_2142_: *mut leanh::LeanObject,
    mut v_inst_2143_: *mut leanh::LeanObject,
    mut v_m_2144_: *mut leanh::LeanObject,
    mut v_k_2145_: *mut leanh::LeanObject,
    mut v_defVal_2146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ofDataValue_x3f_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2147_ = leanh::lean_ctor_get(v_inst_2143_, 1);
    leanh::lean_inc_ref(v_ofDataValue_x3f_2147_);
    leanh::lean_dec_ref(v_inst_2143_);
    v___x_2148_ = l_Lean_KVMap_findCore(v_m_2144_, v_k_2145_);
    if leanh::lean_obj_tag(v___x_2148_) == 0 {
        leanh::lean_dec_ref(v_ofDataValue_x3f_2147_);
        leanh::lean_inc(v_defVal_2146_);
        return v_defVal_2146_;
    } else {
        let mut v_val_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_2149_ = leanh::lean_ctor_get(v___x_2148_, 0);
        leanh::lean_inc(v_val_2149_);
        leanh::lean_dec_ref_known(v___x_2148_, 1);
        v___x_2150_ = leanh::lean_apply_1(v_ofDataValue_x3f_2147_, v_val_2149_);
        if leanh::lean_obj_tag(v___x_2150_) == 0 {
            leanh::lean_inc(v_defVal_2146_);
            return v_defVal_2146_;
        } else {
            let mut v_val_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_2151_ = leanh::lean_ctor_get(v___x_2150_, 0);
            leanh::lean_inc(v_val_2151_);
            leanh::lean_dec_ref_known(v___x_2150_, 1);
            return v_val_2151_;
        }
    }
}
pub unsafe fn l_Lean_KVMap_get___boxed(
    mut v_00_u03b1_2152_: *mut leanh::LeanObject,
    mut v_inst_2153_: *mut leanh::LeanObject,
    mut v_m_2154_: *mut leanh::LeanObject,
    mut v_k_2155_: *mut leanh::LeanObject,
    mut v_defVal_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lean_KVMap_get(
        v_00_u03b1_2152_,
        v_inst_2153_,
        v_m_2154_,
        v_k_2155_,
        v_defVal_2156_,
    );
    leanh::lean_dec(v_defVal_2156_);
    leanh::lean_dec(v_k_2155_);
    leanh::lean_dec(v_m_2154_);
    return v_res_2157_;
}
pub unsafe fn l_Lean_KVMap_set___redArg(
    mut v_inst_2158_: *mut leanh::LeanObject,
    mut v_m_2159_: *mut leanh::LeanObject,
    mut v_k_2160_: *mut leanh::LeanObject,
    mut v_v_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toDataValue_2162_ = leanh::lean_ctor_get(v_inst_2158_, 0);
    leanh::lean_inc_ref(v_toDataValue_2162_);
    leanh::lean_dec_ref(v_inst_2158_);
    v___x_2163_ = leanh::lean_apply_1(v_toDataValue_2162_, v_v_2161_);
    v___x_2164_ = l_Lean_KVMap_insertCore(v_m_2159_, v_k_2160_, v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_KVMap_set(
    mut v_00_u03b1_2165_: *mut leanh::LeanObject,
    mut v_inst_2166_: *mut leanh::LeanObject,
    mut v_m_2167_: *mut leanh::LeanObject,
    mut v_k_2168_: *mut leanh::LeanObject,
    mut v_v_2169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toDataValue_2170_ = leanh::lean_ctor_get(v_inst_2166_, 0);
    leanh::lean_inc_ref(v_toDataValue_2170_);
    leanh::lean_dec_ref(v_inst_2166_);
    v___x_2171_ = leanh::lean_apply_1(v_toDataValue_2170_, v_v_2169_);
    v___x_2172_ = l_Lean_KVMap_insertCore(v_m_2167_, v_k_2168_, v___x_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_KVMap_update___redArg(
    mut v_inst_2173_: *mut leanh::LeanObject,
    mut v_m_2174_: *mut leanh::LeanObject,
    mut v_k_2175_: *mut leanh::LeanObject,
    mut v_f_2176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2177_ = leanh::lean_ctor_get(v_inst_2173_, 0);
                leanh::lean_inc_ref(v_toDataValue_2177_);
                v_ofDataValue_x3f_2178_ = leanh::lean_ctor_get(v_inst_2173_, 1);
                leanh::lean_inc_ref(v_ofDataValue_x3f_2178_);
                leanh::lean_dec_ref(v_inst_2173_);
                v___x_2186_ = l_Lean_KVMap_findCore(v_m_2174_, v_k_2175_);
                if leanh::lean_obj_tag(v___x_2186_) == 0 {
                    leanh::lean_dec_ref(v_ofDataValue_x3f_2178_);
                    v___x_2187_ = leanh::lean_box(0);
                    v___y_2180_ = v___x_2187_;
                    state = 1;
                    continue;
                } else {
                    v_val_2188_ = leanh::lean_ctor_get(v___x_2186_, 0);
                    leanh::lean_inc(v_val_2188_);
                    leanh::lean_dec_ref_known(v___x_2186_, 1);
                    v___x_2189_ = leanh::lean_apply_1(v_ofDataValue_x3f_2178_, v_val_2188_);
                    v___y_2180_ = v___x_2189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2181_ = leanh::lean_apply_1(v_f_2176_, v___y_2180_);
                if leanh::lean_obj_tag(v___x_2181_) == 0 {
                    leanh::lean_dec_ref(v_toDataValue_2177_);
                    v___x_2182_ = l_Lean_KVMap_erase(v_m_2174_, v_k_2175_);
                    leanh::lean_dec(v_k_2175_);
                    return v___x_2182_;
                } else {
                    v_val_2183_ = leanh::lean_ctor_get(v___x_2181_, 0);
                    leanh::lean_inc(v_val_2183_);
                    leanh::lean_dec_ref_known(v___x_2181_, 1);
                    v___x_2184_ = leanh::lean_apply_1(v_toDataValue_2177_, v_val_2183_);
                    v___x_2185_ = l_Lean_KVMap_insertCore(v_m_2174_, v_k_2175_, v___x_2184_);
                    return v___x_2185_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_update(
    mut v_00_u03b1_2190_: *mut leanh::LeanObject,
    mut v_inst_2191_: *mut leanh::LeanObject,
    mut v_m_2192_: *mut leanh::LeanObject,
    mut v_k_2193_: *mut leanh::LeanObject,
    mut v_f_2194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toDataValue_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2195_ = leanh::lean_ctor_get(v_inst_2191_, 0);
                leanh::lean_inc_ref(v_toDataValue_2195_);
                v_ofDataValue_x3f_2196_ = leanh::lean_ctor_get(v_inst_2191_, 1);
                leanh::lean_inc_ref(v_ofDataValue_x3f_2196_);
                leanh::lean_dec_ref(v_inst_2191_);
                v___x_2204_ = l_Lean_KVMap_findCore(v_m_2192_, v_k_2193_);
                if leanh::lean_obj_tag(v___x_2204_) == 0 {
                    leanh::lean_dec_ref(v_ofDataValue_x3f_2196_);
                    v___x_2205_ = leanh::lean_box(0);
                    v___y_2198_ = v___x_2205_;
                    state = 1;
                    continue;
                } else {
                    v_val_2206_ = leanh::lean_ctor_get(v___x_2204_, 0);
                    leanh::lean_inc(v_val_2206_);
                    leanh::lean_dec_ref_known(v___x_2204_, 1);
                    v___x_2207_ = leanh::lean_apply_1(v_ofDataValue_x3f_2196_, v_val_2206_);
                    v___y_2198_ = v___x_2207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2199_ = leanh::lean_apply_1(v_f_2194_, v___y_2198_);
                if leanh::lean_obj_tag(v___x_2199_) == 0 {
                    leanh::lean_dec_ref(v_toDataValue_2195_);
                    v___x_2200_ = l_Lean_KVMap_erase(v_m_2192_, v_k_2193_);
                    leanh::lean_dec(v_k_2193_);
                    return v___x_2200_;
                } else {
                    v_val_2201_ = leanh::lean_ctor_get(v___x_2199_, 0);
                    leanh::lean_inc(v_val_2201_);
                    leanh::lean_dec_ref_known(v___x_2199_, 1);
                    v___x_2202_ = leanh::lean_apply_1(v_toDataValue_2195_, v_val_2201_);
                    v___x_2203_ = l_Lean_KVMap_insertCore(v_m_2192_, v_k_2193_, v___x_2202_);
                    return v___x_2203_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueDataValue___lam__0(
    mut v_val_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2209_, 0, v_val_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Lean_KVMap_instValueBool___lam__1(
    mut v_x_2216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_2216_) == 1 {
        let mut v_v_2217_: u8 = 0;
        let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_2217_ = leanh::lean_ctor_get_uint8(v_x_2216_, 0 as u32);
        v___x_2218_ = leanh::lean_box((v_v_2217_) as usize);
        v___x_2219_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2219_, 0, v___x_2218_);
        return v___x_2219_;
    } else {
        let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2220_ = leanh::lean_box(0);
        return v___x_2220_;
    }
}
pub unsafe fn l_Lean_KVMap_instValueBool___lam__1___boxed(
    mut v_x_2221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_KVMap_instValueBool___lam__1(v_x_2221_);
    leanh::lean_dec_ref(v_x_2221_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_KVMap_instValueNat___lam__1(
    mut v_x_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2228_) == 3 {
                    v_v_2229_ = leanh::lean_ctor_get(v_x_2228_, 0);
                    v_isSharedCheck_2236_ = (!leanh::lean_is_exclusive(v_x_2228_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v_x_2228_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2229_);
                        leanh::lean_dec(v_x_2228_);
                        v___x_2231_ = leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2228_);
                    v___x_2237_ = leanh::lean_box(0);
                    return v___x_2237_;
                }
            }
            1 => {
                if v_isShared_2232_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2231_, 1);
                    v___x_2234_ = v___x_2231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_v_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2235_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueInt___lam__1(
    mut v_x_2243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2243_) == 4 {
                    v_v_2244_ = leanh::lean_ctor_get(v_x_2243_, 0);
                    v_isSharedCheck_2251_ = (!leanh::lean_is_exclusive(v_x_2243_)) as u8;
                    if v_isSharedCheck_2251_ == 0 {
                        v___x_2246_ = v_x_2243_;
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2244_);
                        leanh::lean_dec(v_x_2243_);
                        v___x_2246_ = leanh::lean_box(0);
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2243_);
                    v___x_2252_ = leanh::lean_box(0);
                    return v___x_2252_;
                }
            }
            1 => {
                if v_isShared_2247_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2246_, 1);
                    v___x_2249_ = v___x_2246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_v_2244_);
                    v___x_2249_ = v_reuseFailAlloc_2250_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2249_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueName___lam__1(
    mut v_x_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2258_) == 2 {
                    v_v_2259_ = leanh::lean_ctor_get(v_x_2258_, 0);
                    v_isSharedCheck_2266_ = (!leanh::lean_is_exclusive(v_x_2258_)) as u8;
                    if v_isSharedCheck_2266_ == 0 {
                        v___x_2261_ = v_x_2258_;
                        v_isShared_2262_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2259_);
                        leanh::lean_dec(v_x_2258_);
                        v___x_2261_ = leanh::lean_box(0);
                        v_isShared_2262_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2258_);
                    v___x_2267_ = leanh::lean_box(0);
                    return v___x_2267_;
                }
            }
            1 => {
                if v_isShared_2262_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2261_, 1);
                    v___x_2264_ = v___x_2261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_v_2259_);
                    v___x_2264_ = v_reuseFailAlloc_2265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2264_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueString___lam__1(
    mut v_x_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2273_) == 0 {
                    v_v_2274_ = leanh::lean_ctor_get(v_x_2273_, 0);
                    v_isSharedCheck_2281_ = (!leanh::lean_is_exclusive(v_x_2273_)) as u8;
                    if v_isSharedCheck_2281_ == 0 {
                        v___x_2276_ = v_x_2273_;
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2274_);
                        leanh::lean_dec(v_x_2273_);
                        v___x_2276_ = leanh::lean_box(0);
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2273_);
                    v___x_2282_ = leanh::lean_box(0);
                    return v___x_2282_;
                }
            }
            1 => {
                if v_isShared_2277_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2276_, 1);
                    v___x_2279_ = v___x_2276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_v_2274_);
                    v___x_2279_ = v_reuseFailAlloc_2280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueSyntax___lam__1(
    mut v_x_2288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2288_) == 5 {
                    v_v_2289_ = leanh::lean_ctor_get(v_x_2288_, 0);
                    v_isSharedCheck_2296_ = (!leanh::lean_is_exclusive(v_x_2288_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2291_ = v_x_2288_;
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2289_);
                        leanh::lean_dec(v_x_2288_);
                        v___x_2291_ = leanh::lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2288_);
                    v___x_2297_ = leanh::lean_box(0);
                    return v___x_2297_;
                }
            }
            1 => {
                if v_isShared_2292_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2291_, 1);
                    v___x_2294_ = v___x_2291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_v_2289_);
                    v___x_2294_ = v_reuseFailAlloc_2295_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2294_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_KVMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Format_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedKVMap_default = _init_l_Lean_instInhabitedKVMap_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedKVMap_default);
    l_Lean_instInhabitedKVMap = _init_l_Lean_instInhabitedKVMap();
    leanh::lean_mark_persistent(l_Lean_instInhabitedKVMap);
    l_Lean_KVMap_empty = _init_l_Lean_KVMap_empty();
    leanh::lean_mark_persistent(l_Lean_KVMap_empty);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_KVMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_KVMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Format_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_KVMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_KVMap(builtin);
}