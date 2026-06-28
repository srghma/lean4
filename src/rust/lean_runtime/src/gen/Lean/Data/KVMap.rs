// Lean compiler output
// Module: Lean.Data.KVMap
// Imports: Init.Data.Format.Syntax Init.Data.ToString.Name Init.Data.ToString.Extra
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_length;
use crate::lean_imports_rs::Init::Prelude::{
    lean_name_eq, lean_nat_dec_eq, lean_nat_dec_le, lean_string_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_instInhabitedDataValue_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
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
static mut l_Lean_instInhabitedDataValue_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__0_value) as *mut LeanObject;
pub static l_Lean_instInhabitedDataValue_default___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instInhabitedDataValue_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedDataValue_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instInhabitedDataValue_default___closed__1_value) as *mut LeanObject;
pub static l_Lean_instBEqDataValue___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instBEqDataValue_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instBEqDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instBEqDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__0_value: LeanStringObject<24> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 83, 116,
            114, 105, 110, 103, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__2_value) as *mut LeanObject;
static mut l_Lean_instReprDataValue_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDataValue_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprDataValue_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDataValue_repr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDataValue_repr___closed__5_value: LeanStringObject<22> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 66, 111,
            111, 108, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__6_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__6_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__7_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__8_value: LeanStringObject<22> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 78, 97,
            109, 101, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__8_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__9_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__9_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__10_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__9_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__10_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__11_value: LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 78, 97,
            116, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__11_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__12_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__11_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__12_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__13_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__12_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__13_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__14_value: LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 73, 110,
            116, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__14_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__15_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__14_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__15_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__16_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__15_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__16_value) as *mut LeanObject;
static mut l_Lean_instReprDataValue_repr___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprDataValue_repr___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprDataValue_repr___closed__18_value: LeanStringObject<24> =
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
            76, 101, 97, 110, 46, 68, 97, 116, 97, 86, 97, 108, 117, 101, 46, 111, 102, 83, 121,
            110, 116, 97, 120, 0,
        ],
    };
static mut l_Lean_instReprDataValue_repr___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__18_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__19_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__18_value) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__19_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue_repr___closed__20_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__19_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_instReprDataValue_repr___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue_repr___closed__20_value) as *mut LeanObject;
pub static l_Lean_instReprDataValue___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprDataValue_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_DataValue_str___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_DataValue_str___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_DataValue_str___closed__0_value) as *mut LeanObject;
pub static l_Lean_DataValue_str___closed__1_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_DataValue_str___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_DataValue_str___closed__1_value) as *mut LeanObject;
pub static l_Lean_instToStringDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: lean_data_value_to_string as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instToStringDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instToStringDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeStringDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeStringDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeStringDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeStringDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeBoolDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeBoolDataValue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeBoolDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeBoolDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeNameDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeNameDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeNameDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeNameDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeNatDataValue___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instCoeNatDataValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instCoeNatDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeNatDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeIntDataValue___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instCoeIntDataValue___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instCoeIntDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeIntDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_instCoeSyntaxDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instCoeSyntaxDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instCoeSyntaxDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instCoeSyntaxDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instInhabitedKVMap_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_instInhabitedKVMap: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [40, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [44, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 5 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [41, 0]};
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value) as *mut LeanObject;
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7_value) as *mut LeanObject;
pub static l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__4_value) as *mut LeanObject] };
static mut l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8_value) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value:
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
    m_data: [91, 93, 0],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__0_value
    ) as *mut LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value:
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
    m_data: [91, 0],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value:
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
    m_data: [93, 0],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value
) as *mut LeanObject;
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2_value
    ) as *mut LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6_value
) as *mut LeanObject;
pub static l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__3_value
    ) as *mut LeanObject],
};
static mut l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7:
    *mut LeanObject = core::ptr::addr_of!(
    l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7_value
) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__0_value: LeanStringObject<3> =
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__1_value: LeanStringObject<8> =
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
        m_data: [101, 110, 116, 114, 105, 101, 115, 0],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__2_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__3_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__4_value: LeanStringObject<5> =
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__5_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__4_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__6_value: LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_instReprKVMap_repr___redArg___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprKVMap_repr___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprKVMap_repr___redArg___closed__8_value: LeanStringObject<3> =
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
static mut l_Lean_instReprKVMap_repr___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_instReprKVMap_repr___redArg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprKVMap_repr___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_instReprKVMap_repr___redArg___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_instReprKVMap_repr___redArg___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_instReprKVMap_repr___redArg___closed__11_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__11_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap_repr___redArg___closed__12_value: LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__8_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_instReprKVMap_repr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap_repr___redArg___closed__12_value) as *mut LeanObject;
pub static l_Lean_instReprKVMap___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instReprKVMap_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_instReprKVMap___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_instReprKVMap: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instReprKVMap___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instToString___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Name_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instToString___closed__1_value: LeanClosureObject<2> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instToStringProd___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 2,
    m_objs: [
        core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_instToStringDataValue___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instToString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instToString___closed__2_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_instToString___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__1_value) as *mut LeanObject],
};
static mut l_Lean_KVMap_instToString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instToString___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_empty: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_KVMap_instBEq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_eqv___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instBEq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instBEq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instBEq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instBEq___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueDataValue___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueDataValue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__1_value: LeanClosureObject<1> =
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
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_KVMap_instValueDataValue___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueDataValue___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__1_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueDataValue___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__2_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueDataValue: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueDataValue___closed__2_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueBool___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_instValueBool___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instValueBool___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueBool___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeBoolDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueBool___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueBool: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueBool___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_instValueNat___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instValueNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueNat___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeNatDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueNat___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueNat___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_instValueInt___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instValueInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueInt___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeIntDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueInt___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueInt___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueName___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_KVMap_instValueName___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_KVMap_instValueName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueName___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeNameDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueName___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueName: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueName___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueString___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueString___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeStringDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueString: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueString___closed__1_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueSyntax___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_KVMap_instValueSyntax___lam__1 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_KVMap_instValueSyntax___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__0_value) as *mut LeanObject;
pub static l_Lean_KVMap_instValueSyntax___closed__1_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_instCoeSyntaxDataValue___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_KVMap_instValueSyntax___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__1_value) as *mut LeanObject;
pub static mut l_Lean_KVMap_instValueSyntax: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_KVMap_instValueSyntax___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_DataValue_ctorIdx(mut v_x_1152_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1152_) {
        0 => {
            let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
            v___x_1153_ = lean_unsigned_to_nat(0);
            return v___x_1153_;
        }
        1 => {
            let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
            v___x_1154_ = lean_unsigned_to_nat(1);
            return v___x_1154_;
        }
        2 => {
            let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
            v___x_1155_ = lean_unsigned_to_nat(2);
            return v___x_1155_;
        }
        3 => {
            let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
            v___x_1156_ = lean_unsigned_to_nat(3);
            return v___x_1156_;
        }
        4 => {
            let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
            v___x_1157_ = lean_unsigned_to_nat(4);
            return v___x_1157_;
        }
        _ => {
            let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
            v___x_1158_ = lean_unsigned_to_nat(5);
            return v___x_1158_;
        }
    }
}
pub unsafe fn l_Lean_DataValue_ctorIdx___boxed(mut v_x_1159_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1160_: *mut LeanObject = core::ptr::null_mut();
    v_res_1160_ = l_Lean_DataValue_ctorIdx(v_x_1159_);
    lean_dec_ref(v_x_1159_);
    return v_res_1160_;
}
pub unsafe fn l_Lean_DataValue_ctorElim___redArg(
    mut v_t_1161_: *mut LeanObject,
    mut v_k_1162_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1161_) {
        0 => {
            let mut v_v_1163_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
            v_v_1163_ = lean_ctor_get(v_t_1161_, 0);
            lean_inc_ref(v_v_1163_);
            lean_dec_ref_known(v_t_1161_, 1);
            v___x_1164_ = lean_apply_1(v_k_1162_, v_v_1163_);
            return v___x_1164_;
        }
        1 => {
            let mut v_v_1165_: u8 = 0;
            let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
            v_v_1165_ = lean_ctor_get_uint8(v_t_1161_, 0 as u32);
            lean_dec_ref_known(v_t_1161_, 0);
            v___x_1166_ = lean_box((v_v_1165_) as usize);
            v___x_1167_ = lean_apply_1(v_k_1162_, v___x_1166_);
            return v___x_1167_;
        }
        _ => {
            let mut v_v_1168_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
            v_v_1168_ = lean_ctor_get(v_t_1161_, 0);
            lean_inc(v_v_1168_);
            lean_dec_ref(v_t_1161_);
            v___x_1169_ = lean_apply_1(v_k_1162_, v_v_1168_);
            return v___x_1169_;
        }
    }
}
pub unsafe fn l_Lean_DataValue_ctorElim(
    mut v_motive_1170_: *mut LeanObject,
    mut v_ctorIdx_1171_: *mut LeanObject,
    mut v_t_1172_: *mut LeanObject,
    mut v_h_1173_: *mut LeanObject,
    mut v_k_1174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    v___x_1175_ = l_Lean_DataValue_ctorElim___redArg(v_t_1172_, v_k_1174_);
    return v___x_1175_;
}
pub unsafe fn l_Lean_DataValue_ctorElim___boxed(
    mut v_motive_1176_: *mut LeanObject,
    mut v_ctorIdx_1177_: *mut LeanObject,
    mut v_t_1178_: *mut LeanObject,
    mut v_h_1179_: *mut LeanObject,
    mut v_k_1180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v_res_1181_ = l_Lean_DataValue_ctorElim(
        v_motive_1176_,
        v_ctorIdx_1177_,
        v_t_1178_,
        v_h_1179_,
        v_k_1180_,
    );
    lean_dec(v_ctorIdx_1177_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_DataValue_ofString_elim___redArg(
    mut v_t_1182_: *mut LeanObject,
    mut v_ofString_1183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
    v___x_1184_ = l_Lean_DataValue_ctorElim___redArg(v_t_1182_, v_ofString_1183_);
    return v___x_1184_;
}
pub unsafe fn l_Lean_DataValue_ofString_elim(
    mut v_motive_1185_: *mut LeanObject,
    mut v_t_1186_: *mut LeanObject,
    mut v_h_1187_: *mut LeanObject,
    mut v_ofString_1188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lean_DataValue_ctorElim___redArg(v_t_1186_, v_ofString_1188_);
    return v___x_1189_;
}
pub unsafe fn l_Lean_DataValue_ofBool_elim___redArg(
    mut v_t_1190_: *mut LeanObject,
    mut v_ofBool_1191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Lean_DataValue_ctorElim___redArg(v_t_1190_, v_ofBool_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Lean_DataValue_ofBool_elim(
    mut v_motive_1193_: *mut LeanObject,
    mut v_t_1194_: *mut LeanObject,
    mut v_h_1195_: *mut LeanObject,
    mut v_ofBool_1196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    v___x_1197_ = l_Lean_DataValue_ctorElim___redArg(v_t_1194_, v_ofBool_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Lean_DataValue_ofName_elim___redArg(
    mut v_t_1198_: *mut LeanObject,
    mut v_ofName_1199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    v___x_1200_ = l_Lean_DataValue_ctorElim___redArg(v_t_1198_, v_ofName_1199_);
    return v___x_1200_;
}
pub unsafe fn l_Lean_DataValue_ofName_elim(
    mut v_motive_1201_: *mut LeanObject,
    mut v_t_1202_: *mut LeanObject,
    mut v_h_1203_: *mut LeanObject,
    mut v_ofName_1204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    v___x_1205_ = l_Lean_DataValue_ctorElim___redArg(v_t_1202_, v_ofName_1204_);
    return v___x_1205_;
}
pub unsafe fn l_Lean_DataValue_ofNat_elim___redArg(
    mut v_t_1206_: *mut LeanObject,
    mut v_ofNat_1207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    v___x_1208_ = l_Lean_DataValue_ctorElim___redArg(v_t_1206_, v_ofNat_1207_);
    return v___x_1208_;
}
pub unsafe fn l_Lean_DataValue_ofNat_elim(
    mut v_motive_1209_: *mut LeanObject,
    mut v_t_1210_: *mut LeanObject,
    mut v_h_1211_: *mut LeanObject,
    mut v_ofNat_1212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    v___x_1213_ = l_Lean_DataValue_ctorElim___redArg(v_t_1210_, v_ofNat_1212_);
    return v___x_1213_;
}
pub unsafe fn l_Lean_DataValue_ofInt_elim___redArg(
    mut v_t_1214_: *mut LeanObject,
    mut v_ofInt_1215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
    v___x_1216_ = l_Lean_DataValue_ctorElim___redArg(v_t_1214_, v_ofInt_1215_);
    return v___x_1216_;
}
pub unsafe fn l_Lean_DataValue_ofInt_elim(
    mut v_motive_1217_: *mut LeanObject,
    mut v_t_1218_: *mut LeanObject,
    mut v_h_1219_: *mut LeanObject,
    mut v_ofInt_1220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lean_DataValue_ctorElim___redArg(v_t_1218_, v_ofInt_1220_);
    return v___x_1221_;
}
pub unsafe fn l_Lean_DataValue_ofSyntax_elim___redArg(
    mut v_t_1222_: *mut LeanObject,
    mut v_ofSyntax_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    v___x_1224_ = l_Lean_DataValue_ctorElim___redArg(v_t_1222_, v_ofSyntax_1223_);
    return v___x_1224_;
}
pub unsafe fn l_Lean_DataValue_ofSyntax_elim(
    mut v_motive_1225_: *mut LeanObject,
    mut v_t_1226_: *mut LeanObject,
    mut v_h_1227_: *mut LeanObject,
    mut v_ofSyntax_1228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_DataValue_ctorElim___redArg(v_t_1226_, v_ofSyntax_1228_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_instBEqDataValue_beq(
    mut v_x_1235_: *mut LeanObject,
    mut v_x_1236_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1235_) {
        0 => {
            if lean_obj_tag(v_x_1236_) == 0 {
                let mut v_v_1237_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_1238_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1239_: u8 = 0;
                v_v_1237_ = lean_ctor_get(v_x_1235_, 0);
                lean_inc_ref(v_v_1237_);
                lean_dec_ref_known(v_x_1235_, 1);
                v_v_1238_ = lean_ctor_get(v_x_1236_, 0);
                lean_inc_ref(v_v_1238_);
                lean_dec_ref_known(v_x_1236_, 1);
                v___x_1239_ = lean_string_dec_eq(v_v_1237_, v_v_1238_);
                lean_dec_ref(v_v_1238_);
                lean_dec_ref(v_v_1237_);
                return v___x_1239_;
            } else {
                let mut v___x_1240_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 1);
                lean_dec_ref(v_x_1236_);
                v___x_1240_ = 0;
                return v___x_1240_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_1236_) == 1 {
                let mut v_v_1241_: u8 = 0;
                v_v_1241_ = lean_ctor_get_uint8(v_x_1235_, 0 as u32);
                lean_dec_ref_known(v_x_1235_, 0);
                if v_v_1241_ == 0 {
                    let mut v_v_1242_: u8 = 0;
                    v_v_1242_ = lean_ctor_get_uint8(v_x_1236_, 0 as u32);
                    lean_dec_ref_known(v_x_1236_, 0);
                    if v_v_1242_ == 0 {
                        let mut v___x_1243_: u8 = 0;
                        v___x_1243_ = 1;
                        return v___x_1243_;
                    } else {
                        return v_v_1241_;
                    }
                } else {
                    let mut v_v_1244_: u8 = 0;
                    v_v_1244_ = lean_ctor_get_uint8(v_x_1236_, 0 as u32);
                    lean_dec_ref_known(v_x_1236_, 0);
                    return v_v_1244_;
                }
            } else {
                let mut v___x_1245_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 0);
                lean_dec_ref(v_x_1236_);
                v___x_1245_ = 0;
                return v___x_1245_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_1236_) == 2 {
                let mut v_v_1246_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_1247_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: u8 = 0;
                v_v_1246_ = lean_ctor_get(v_x_1235_, 0);
                lean_inc(v_v_1246_);
                lean_dec_ref_known(v_x_1235_, 1);
                v_v_1247_ = lean_ctor_get(v_x_1236_, 0);
                lean_inc(v_v_1247_);
                lean_dec_ref_known(v_x_1236_, 1);
                v___x_1248_ = lean_name_eq(v_v_1246_, v_v_1247_);
                lean_dec(v_v_1247_);
                lean_dec(v_v_1246_);
                return v___x_1248_;
            } else {
                let mut v___x_1249_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 1);
                lean_dec_ref(v_x_1236_);
                v___x_1249_ = 0;
                return v___x_1249_;
            }
        }
        3 => {
            if lean_obj_tag(v_x_1236_) == 3 {
                let mut v_v_1250_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_1251_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1252_: u8 = 0;
                v_v_1250_ = lean_ctor_get(v_x_1235_, 0);
                lean_inc(v_v_1250_);
                lean_dec_ref_known(v_x_1235_, 1);
                v_v_1251_ = lean_ctor_get(v_x_1236_, 0);
                lean_inc(v_v_1251_);
                lean_dec_ref_known(v_x_1236_, 1);
                v___x_1252_ = lean_nat_dec_eq(v_v_1250_, v_v_1251_);
                lean_dec(v_v_1251_);
                lean_dec(v_v_1250_);
                return v___x_1252_;
            } else {
                let mut v___x_1253_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 1);
                lean_dec_ref(v_x_1236_);
                v___x_1253_ = 0;
                return v___x_1253_;
            }
        }
        4 => {
            if lean_obj_tag(v_x_1236_) == 4 {
                let mut v_v_1254_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_1255_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1256_: u8 = 0;
                v_v_1254_ = lean_ctor_get(v_x_1235_, 0);
                lean_inc(v_v_1254_);
                lean_dec_ref_known(v_x_1235_, 1);
                v_v_1255_ = lean_ctor_get(v_x_1236_, 0);
                lean_inc(v_v_1255_);
                lean_dec_ref_known(v_x_1236_, 1);
                v___x_1256_ = lean_int_dec_eq(v_v_1254_, v_v_1255_);
                lean_dec(v_v_1255_);
                lean_dec(v_v_1254_);
                return v___x_1256_;
            } else {
                let mut v___x_1257_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 1);
                lean_dec_ref(v_x_1236_);
                v___x_1257_ = 0;
                return v___x_1257_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_1236_) == 5 {
                let mut v_v_1258_: *mut LeanObject = core::ptr::null_mut();
                let mut v_v_1259_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1260_: u8 = 0;
                v_v_1258_ = lean_ctor_get(v_x_1235_, 0);
                lean_inc(v_v_1258_);
                lean_dec_ref_known(v_x_1235_, 1);
                v_v_1259_ = lean_ctor_get(v_x_1236_, 0);
                lean_inc(v_v_1259_);
                lean_dec_ref_known(v_x_1236_, 1);
                v___x_1260_ = l_Lean_Syntax_structEq(v_v_1258_, v_v_1259_);
                return v___x_1260_;
            } else {
                let mut v___x_1261_: u8 = 0;
                lean_dec_ref_known(v_x_1235_, 1);
                lean_dec_ref(v_x_1236_);
                v___x_1261_ = 0;
                return v___x_1261_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqDataValue_beq___boxed(
    mut v_x_1262_: *mut LeanObject,
    mut v_x_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1264_: u8 = 0;
    let mut v_r_1265_: *mut LeanObject = core::ptr::null_mut();
    v_res_1264_ = l_Lean_instBEqDataValue_beq(v_x_1262_, v_x_1263_);
    v_r_1265_ = lean_box((v_res_1264_) as usize);
    return v_r_1265_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__3() -> *mut LeanObject {
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    v___x_1274_ = lean_unsigned_to_nat(2);
    v___x_1275_ = lean_nat_to_int(v___x_1274_);
    return v___x_1275_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__4() -> *mut LeanObject {
    let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    v___x_1276_ = lean_unsigned_to_nat(1);
    v___x_1277_ = lean_nat_to_int(v___x_1276_);
    return v___x_1277_;
}
pub unsafe fn _init_l_Lean_instReprDataValue_repr___closed__17() -> *mut LeanObject {
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    v___x_1302_ = lean_unsigned_to_nat(0);
    v___x_1303_ = lean_nat_to_int(v___x_1302_);
    return v___x_1303_;
}
pub unsafe fn l_Lean_instReprDataValue_repr(
    mut v_x_1310_: *mut LeanObject,
    mut v_prec_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: u8 = 0;
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1324_: u8 = 0;
    let mut v___y_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: u8 = 0;
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1341_: u8 = 0;
    let mut v_v_1342_: u8 = 0;
    let mut v___y_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: u8 = 0;
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: u8 = 0;
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___y_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1388_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1391_: u8 = 0;
    let mut v_v_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1395_: u8 = 0;
    let mut v___y_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: u8 = 0;
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1415_: u8 = 0;
    let mut v_v_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: u8 = 0;
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1310_) {
                0 => {
                    v_v_1321_ = lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1341_ = (!lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1341_ == 0 {
                        v___x_1323_ = v_x_1310_;
                        v_isShared_1324_ = v_isSharedCheck_1341_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_v_1321_);
                        lean_dec(v_x_1310_);
                        v___x_1323_ = lean_box(0);
                        v_isShared_1324_ = v_isSharedCheck_1341_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_v_1342_ = lean_ctor_get_uint8(v_x_1310_, 0 as u32);
                    lean_dec_ref_known(v_x_1310_, 0);
                    v___x_1352_ = lean_unsigned_to_nat(1024);
                    v___x_1353_ = lean_nat_dec_le(v___x_1352_, v_prec_1311_);
                    if v___x_1353_ == 0 {
                        v___x_1354_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1344_ = v___x_1354_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1355_ = lean_obj_once(
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
                    v_v_1356_ = lean_ctor_get(v_x_1310_, 0);
                    lean_inc(v_v_1356_);
                    lean_dec_ref_known(v_x_1310_, 1);
                    v___x_1367_ = lean_unsigned_to_nat(1024);
                    v___x_1368_ = lean_nat_dec_le(v___x_1367_, v_prec_1311_);
                    if v___x_1368_ == 0 {
                        v___x_1369_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1358_ = v___x_1369_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1370_ = lean_obj_once(
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
                    v_v_1371_ = lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1391_ = (!lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1391_ == 0 {
                        v___x_1373_ = v_x_1310_;
                        v_isShared_1374_ = v_isSharedCheck_1391_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_v_1371_);
                        lean_dec(v_x_1310_);
                        v___x_1373_ = lean_box(0);
                        v_isShared_1374_ = v_isSharedCheck_1391_;
                        state = 7;
                        continue;
                    }
                }
                4 => {
                    v_v_1392_ = lean_ctor_get(v_x_1310_, 0);
                    v_isSharedCheck_1415_ = (!lean_is_exclusive(v_x_1310_)) as u8;
                    if v_isSharedCheck_1415_ == 0 {
                        v___x_1394_ = v_x_1310_;
                        v_isShared_1395_ = v_isSharedCheck_1415_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_v_1392_);
                        lean_dec(v_x_1310_);
                        v___x_1394_ = lean_box(0);
                        v_isShared_1395_ = v_isSharedCheck_1415_;
                        state = 10;
                        continue;
                    }
                }
                _ => {
                    v_v_1416_ = lean_ctor_get(v_x_1310_, 0);
                    lean_inc(v_v_1416_);
                    lean_dec_ref_known(v_x_1310_, 1);
                    v___x_1427_ = lean_unsigned_to_nat(1024);
                    v___x_1428_ = lean_nat_dec_le(v___x_1427_, v_prec_1311_);
                    if v___x_1428_ == 0 {
                        v___x_1429_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                            _init_l_Lean_instReprDataValue_repr___closed__3,
                        );
                        v___y_1418_ = v___x_1429_;
                        state = 14;
                        continue;
                    } else {
                        v___x_1430_ = lean_obj_once(
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
                lean_inc(v___y_1314_);
                v___x_1316_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1316_, 0, v___y_1314_);
                lean_ctor_set(v___x_1316_, 1, v___y_1315_);
                lean_inc(v___y_1313_);
                v___x_1317_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1317_, 0, v___y_1313_);
                lean_ctor_set(v___x_1317_, 1, v___x_1316_);
                v___x_1318_ = 0;
                v___x_1319_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1319_, 0, v___x_1317_);
                lean_ctor_set_uint8(
                    v___x_1319_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1318_,
                );
                v___x_1320_ = l_Repr_addAppParen(v___x_1319_, v_prec_1311_);
                return v___x_1320_;
            }
            2 => {
                v___x_1337_ = lean_unsigned_to_nat(1024);
                v___x_1338_ = lean_nat_dec_le(v___x_1337_, v_prec_1311_);
                if v___x_1338_ == 0 {
                    v___x_1339_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1326_ = v___x_1339_;
                    state = 3;
                    continue;
                } else {
                    v___x_1340_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_1323_, 3);
                    lean_ctor_set(v___x_1323_, 0, v___x_1328_);
                    v___x_1330_ = v___x_1323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
                    v___x_1330_ = v_reuseFailAlloc_1336_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1331_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1331_, 0, v___x_1327_);
                lean_ctor_set(v___x_1331_, 1, v___x_1330_);
                lean_inc(v___y_1326_);
                v___x_1332_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1332_, 0, v___y_1326_);
                lean_ctor_set(v___x_1332_, 1, v___x_1331_);
                v___x_1333_ = 0;
                v___x_1334_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1334_, 0, v___x_1332_);
                lean_ctor_set_uint8(
                    v___x_1334_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1333_,
                );
                v___x_1335_ = l_Repr_addAppParen(v___x_1334_, v_prec_1311_);
                return v___x_1335_;
            }
            5 => {
                v___x_1345_ = l_Lean_instReprDataValue_repr___closed__7;
                v___x_1346_ = l_Bool_repr___redArg(v_v_1342_);
                v___x_1347_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1347_, 0, v___x_1345_);
                lean_ctor_set(v___x_1347_, 1, v___x_1346_);
                lean_inc(v___y_1344_);
                v___x_1348_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1348_, 0, v___y_1344_);
                lean_ctor_set(v___x_1348_, 1, v___x_1347_);
                v___x_1349_ = 0;
                v___x_1350_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1350_, 0, v___x_1348_);
                lean_ctor_set_uint8(
                    v___x_1350_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1349_,
                );
                v___x_1351_ = l_Repr_addAppParen(v___x_1350_, v_prec_1311_);
                return v___x_1351_;
            }
            6 => {
                v___x_1359_ = l_Lean_instReprDataValue_repr___closed__10;
                v___x_1360_ = lean_unsigned_to_nat(1024);
                v___x_1361_ = l_Lean_Name_reprPrec(v_v_1356_, v___x_1360_);
                v___x_1362_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1362_, 0, v___x_1359_);
                lean_ctor_set(v___x_1362_, 1, v___x_1361_);
                lean_inc(v___y_1358_);
                v___x_1363_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1363_, 0, v___y_1358_);
                lean_ctor_set(v___x_1363_, 1, v___x_1362_);
                v___x_1364_ = 0;
                v___x_1365_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1365_, 0, v___x_1363_);
                lean_ctor_set_uint8(
                    v___x_1365_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1364_,
                );
                v___x_1366_ = l_Repr_addAppParen(v___x_1365_, v_prec_1311_);
                return v___x_1366_;
            }
            7 => {
                v___x_1387_ = lean_unsigned_to_nat(1024);
                v___x_1388_ = lean_nat_dec_le(v___x_1387_, v_prec_1311_);
                if v___x_1388_ == 0 {
                    v___x_1389_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1376_ = v___x_1389_;
                    state = 8;
                    continue;
                } else {
                    v___x_1390_ = lean_obj_once(
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
                    lean_ctor_set(v___x_1373_, 0, v___x_1378_);
                    v___x_1380_ = v___x_1373_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1386_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1378_);
                    v___x_1380_ = v_reuseFailAlloc_1386_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1381_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1381_, 0, v___x_1377_);
                lean_ctor_set(v___x_1381_, 1, v___x_1380_);
                lean_inc(v___y_1376_);
                v___x_1382_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1382_, 0, v___y_1376_);
                lean_ctor_set(v___x_1382_, 1, v___x_1381_);
                v___x_1383_ = 0;
                v___x_1384_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1384_, 0, v___x_1382_);
                lean_ctor_set_uint8(
                    v___x_1384_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1383_,
                );
                v___x_1385_ = l_Repr_addAppParen(v___x_1384_, v_prec_1311_);
                return v___x_1385_;
            }
            10 => {
                v___x_1411_ = lean_unsigned_to_nat(1024);
                v___x_1412_ = lean_nat_dec_le(v___x_1411_, v_prec_1311_);
                if v___x_1412_ == 0 {
                    v___x_1413_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__3_once),
                        _init_l_Lean_instReprDataValue_repr___closed__3,
                    );
                    v___y_1397_ = v___x_1413_;
                    state = 11;
                    continue;
                } else {
                    v___x_1414_ = lean_obj_once(
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
                v___x_1399_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17_once),
                    _init_l_Lean_instReprDataValue_repr___closed__17,
                );
                v___x_1400_ = lean_int_dec_lt(v_v_1392_, v___x_1399_);
                if v___x_1400_ == 0 {
                    v___x_1401_ = l_Int_repr(v_v_1392_);
                    lean_dec(v_v_1392_);
                    if v_isShared_1395_ == 0 {
                        lean_ctor_set_tag(v___x_1394_, 3);
                        lean_ctor_set(v___x_1394_, 0, v___x_1401_);
                        v___x_1403_ = v___x_1394_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1404_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
                        v___x_1403_ = v_reuseFailAlloc_1404_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___x_1405_ = lean_unsigned_to_nat(1024);
                    v___x_1406_ = l_Int_repr(v_v_1392_);
                    lean_dec(v_v_1392_);
                    if v_isShared_1395_ == 0 {
                        lean_ctor_set_tag(v___x_1394_, 3);
                        lean_ctor_set(v___x_1394_, 0, v___x_1406_);
                        v___x_1408_ = v___x_1394_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_1410_ = lean_alloc_ctor(3, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1406_);
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
                v___x_1420_ = lean_unsigned_to_nat(1024);
                v___x_1421_ = l_Lean_Syntax_instRepr_repr(v_v_1416_, v___x_1420_);
                v___x_1422_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1422_, 0, v___x_1419_);
                lean_ctor_set(v___x_1422_, 1, v___x_1421_);
                lean_inc(v___y_1418_);
                v___x_1423_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1423_, 0, v___y_1418_);
                lean_ctor_set(v___x_1423_, 1, v___x_1422_);
                v___x_1424_ = 0;
                v___x_1425_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1425_, 0, v___x_1423_);
                lean_ctor_set_uint8(
                    v___x_1425_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_1431_: *mut LeanObject,
    mut v_prec_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1433_: *mut LeanObject = core::ptr::null_mut();
    v_res_1433_ = l_Lean_instReprDataValue_repr(v_x_1431_, v_prec_1432_);
    lean_dec(v_prec_1432_);
    return v_res_1433_;
}
pub unsafe fn lean_data_value_beq(
    mut v_a_1436_: *mut LeanObject,
    mut v_b_1437_: *mut LeanObject,
) -> u8 {
    let mut v___x_1438_: u8 = 0;
    v___x_1438_ = l_Lean_instBEqDataValue_beq(v_a_1436_, v_b_1437_);
    return v___x_1438_;
}
pub unsafe fn l_Lean_DataValue_beqExp___boxed(
    mut v_a_1439_: *mut LeanObject,
    mut v_b_1440_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut LeanObject = core::ptr::null_mut();
    v_res_1441_ = lean_data_value_beq(v_a_1439_, v_b_1440_);
    v_r_1442_ = lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn lean_mk_bool_data_value(mut v_b_1443_: u8) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1444_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_1444_, 0 as u32, v_b_1443_);
    return v___x_1444_;
}
pub unsafe fn l_Lean_mkBoolDataValueEx___boxed(mut v_b_1445_: *mut LeanObject) -> *mut LeanObject {
    let mut v_b_boxed_1446_: u8 = 0;
    let mut v_res_1447_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1446_ = (lean_unbox(v_b_1445_) as u8);
    v_res_1447_ = lean_mk_bool_data_value(v_b_boxed_1446_);
    return v_res_1447_;
}
pub unsafe fn lean_data_value_bool(mut v_x_1448_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1448_) == 1 {
        let mut v_v_1449_: u8 = 0;
        v_v_1449_ = lean_ctor_get_uint8(v_x_1448_, 0 as u32);
        lean_dec_ref_known(v_x_1448_, 0);
        return v_v_1449_;
    } else {
        let mut v___x_1450_: u8 = 0;
        lean_dec_ref(v_x_1448_);
        v___x_1450_ = 0;
        return v___x_1450_;
    }
}
pub unsafe fn l_Lean_DataValue_getBoolEx___boxed(
    mut v_x_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1452_: u8 = 0;
    let mut v_r_1453_: *mut LeanObject = core::ptr::null_mut();
    v_res_1452_ = lean_data_value_bool(v_x_1451_);
    v_r_1453_ = lean_box((v_res_1452_) as usize);
    return v_r_1453_;
}
pub unsafe fn l_Lean_DataValue_sameCtor(
    mut v_x_1454_: *mut LeanObject,
    mut v_x_1455_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1454_) {
        0 => {
            if lean_obj_tag(v_x_1455_) == 0 {
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
            if lean_obj_tag(v_x_1455_) == 1 {
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
            if lean_obj_tag(v_x_1455_) == 2 {
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
            if lean_obj_tag(v_x_1455_) == 3 {
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
            if lean_obj_tag(v_x_1455_) == 4 {
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
            if lean_obj_tag(v_x_1455_) == 5 {
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
    mut v_x_1468_: *mut LeanObject,
    mut v_x_1469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1470_: u8 = 0;
    let mut v_r_1471_: *mut LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_DataValue_sameCtor(v_x_1468_, v_x_1469_);
    lean_dec_ref(v_x_1469_);
    lean_dec_ref(v_x_1468_);
    v_r_1471_ = lean_box((v_res_1470_) as usize);
    return v_r_1471_;
}
pub unsafe fn lean_data_value_to_string(mut v_x_1474_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1474_) {
        0 => {
            let mut v_v_1475_: *mut LeanObject = core::ptr::null_mut();
            v_v_1475_ = lean_ctor_get(v_x_1474_, 0);
            lean_inc_ref(v_v_1475_);
            lean_dec_ref_known(v_x_1474_, 1);
            return v_v_1475_;
        }
        1 => {
            let mut v_v_1476_: u8 = 0;
            v_v_1476_ = lean_ctor_get_uint8(v_x_1474_, 0 as u32);
            lean_dec_ref_known(v_x_1474_, 0);
            if v_v_1476_ == 0 {
                let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
                v___x_1477_ = l_Lean_DataValue_str___closed__0;
                return v___x_1477_;
            } else {
                let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
                v___x_1478_ = l_Lean_DataValue_str___closed__1;
                return v___x_1478_;
            }
        }
        2 => {
            let mut v_v_1479_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1480_: u8 = 0;
            let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
            v_v_1479_ = lean_ctor_get(v_x_1474_, 0);
            lean_inc(v_v_1479_);
            lean_dec_ref_known(v_x_1474_, 1);
            v___x_1480_ = 1;
            v___x_1481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                v_v_1479_,
                v___x_1480_,
            );
            return v___x_1481_;
        }
        3 => {
            let mut v_v_1482_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
            v_v_1482_ = lean_ctor_get(v_x_1474_, 0);
            lean_inc(v_v_1482_);
            lean_dec_ref_known(v_x_1474_, 1);
            v___x_1483_ = l_Nat_reprFast(v_v_1482_);
            return v___x_1483_;
        }
        4 => {
            let mut v_v_1484_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
            v_v_1484_ = lean_ctor_get(v_x_1474_, 0);
            lean_inc(v_v_1484_);
            lean_dec_ref_known(v_x_1474_, 1);
            v___x_1485_ = l_Int_repr(v_v_1484_);
            lean_dec(v_v_1484_);
            return v___x_1485_;
        }
        _ => {
            let mut v_v_1486_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1488_: u8 = 0;
            let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
            v_v_1486_ = lean_ctor_get(v_x_1474_, 0);
            lean_inc(v_v_1486_);
            lean_dec_ref_known(v_x_1474_, 1);
            v___x_1487_ = lean_box(0);
            v___x_1488_ = 0;
            v___x_1489_ = l_Lean_Syntax_formatStx(v_v_1486_, v___x_1487_, v___x_1488_);
            v___x_1490_ = l_Std_Format_defWidth;
            v___x_1491_ = lean_unsigned_to_nat(0);
            v___x_1492_ = l_Std_Format_pretty(v___x_1489_, v___x_1490_, v___x_1491_, v___x_1491_);
            return v___x_1492_;
        }
    }
}
pub unsafe fn l_Lean_instCoeStringDataValue___lam__0(
    mut v_v_1495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1496_, 0, v_v_1495_);
    return v___x_1496_;
}
pub unsafe fn l_Lean_instCoeBoolDataValue___lam__0(mut v_v_1499_: u8) -> *mut LeanObject {
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v___x_1500_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_1500_, 0 as u32, v_v_1499_);
    return v___x_1500_;
}
pub unsafe fn l_Lean_instCoeBoolDataValue___lam__0___boxed(
    mut v_v_1501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1502_: u8 = 0;
    let mut v_res_1503_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1502_ = (lean_unbox(v_v_1501_) as u8);
    v_res_1503_ = l_Lean_instCoeBoolDataValue___lam__0(v_v_boxed_1502_);
    return v_res_1503_;
}
pub unsafe fn l_Lean_instCoeNameDataValue___lam__0(
    mut v_v_1506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    v___x_1507_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1507_, 0, v_v_1506_);
    return v___x_1507_;
}
pub unsafe fn l_Lean_instCoeNatDataValue___lam__0(
    mut v_v_1510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    v___x_1511_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1511_, 0, v_v_1510_);
    return v___x_1511_;
}
pub unsafe fn l_Lean_instCoeIntDataValue___lam__0(
    mut v_v_1514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    v___x_1515_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1515_, 0, v_v_1514_);
    return v___x_1515_;
}
pub unsafe fn l_Lean_instCoeSyntaxDataValue___lam__0(
    mut v_v_1518_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_1519_, 0, v_v_1518_);
    return v___x_1519_;
}
pub unsafe fn _init_l_Lean_instInhabitedKVMap_default() -> *mut LeanObject {
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    v___x_1522_ = lean_box(0);
    return v___x_1522_;
}
pub unsafe fn _init_l_Lean_instInhabitedKVMap() -> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = lean_box(0);
    return v___x_1523_;
}
pub unsafe fn l_Nat_cast___at___00Lean_instReprKVMap_repr_spec__1(
    mut v_a_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1525_ = lean_nat_to_int(v_a_1524_);
    return v___x_1525_;
}
pub unsafe fn l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(
    mut v_x_1526_: *mut LeanObject,
    mut v_x_1527_: *mut LeanObject,
    mut v_x_1528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1528_) == 0 {
                    lean_dec(v_x_1526_);
                    return v_x_1527_;
                } else {
                    v_head_1529_ = lean_ctor_get(v_x_1528_, 0);
                    v_tail_1530_ = lean_ctor_get(v_x_1528_, 1);
                    v_isSharedCheck_1539_ = (!lean_is_exclusive(v_x_1528_)) as u8;
                    if v_isSharedCheck_1539_ == 0 {
                        v___x_1532_ = v_x_1528_;
                        v_isShared_1533_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1530_);
                        lean_inc(v_head_1529_);
                        lean_dec(v_x_1528_);
                        v___x_1532_ = lean_box(0);
                        v_isShared_1533_ = v_isSharedCheck_1539_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1526_);
                if v_isShared_1533_ == 0 {
                    lean_ctor_set_tag(v___x_1532_, 5);
                    lean_ctor_set(v___x_1532_, 1, v_x_1526_);
                    lean_ctor_set(v___x_1532_, 0, v_x_1527_);
                    v___x_1535_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_x_1527_);
                    lean_ctor_set(v_reuseFailAlloc_1538_, 1, v_x_1526_);
                    v___x_1535_ = v_reuseFailAlloc_1538_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1536_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1536_, 0, v___x_1535_);
                lean_ctor_set(v___x_1536_, 1, v_head_1529_);
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
    mut v_x_1540_: *mut LeanObject,
    mut v_x_1541_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1540_) == 0 {
        let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1541_);
        v___x_1542_ = lean_box(0);
        return v___x_1542_;
    } else {
        let mut v_tail_1543_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1543_ = lean_ctor_get(v_x_1540_, 1);
        if lean_obj_tag(v_tail_1543_) == 0 {
            let mut v_head_1544_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1541_);
            v_head_1544_ = lean_ctor_get(v_x_1540_, 0);
            lean_inc(v_head_1544_);
            lean_dec_ref_known(v_x_1540_, 2);
            return v_head_1544_;
        } else {
            let mut v_head_1545_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1543_);
            v_head_1545_ = lean_ctor_get(v_x_1540_, 0);
            lean_inc(v_head_1545_);
            lean_dec_ref_known(v_x_1540_, 2);
            v___x_1546_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2_spec__3(v_x_1541_, v_head_1545_, v_tail_1543_);
            return v___x_1546_;
        }
    }
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    v___x_1555_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__0;
    v___x_1556_ = lean_string_length(v___x_1555_);
    return v___x_1556_;
}
pub unsafe fn _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__5);
    v___x_1558_ = lean_nat_to_int(v___x_1557_);
    return v___x_1558_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(
    mut v_x_1563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1568_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: u8 = 0;
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1564_ = lean_ctor_get(v_x_1563_, 0);
                v_snd_1565_ = lean_ctor_get(v_x_1563_, 1);
                v_isSharedCheck_1588_ = (!lean_is_exclusive(v_x_1563_)) as u8;
                if v_isSharedCheck_1588_ == 0 {
                    v___x_1567_ = v_x_1563_;
                    v_isShared_1568_ = v_isSharedCheck_1588_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1565_);
                    lean_inc(v_fst_1564_);
                    lean_dec(v_x_1563_);
                    v___x_1567_ = lean_box(0);
                    v_isShared_1568_ = v_isSharedCheck_1588_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1569_ = lean_unsigned_to_nat(0);
                v___x_1570_ = l_Lean_Name_reprPrec(v_fst_1564_, v___x_1569_);
                v___x_1571_ = lean_box(0);
                if v_isShared_1568_ == 0 {
                    lean_ctor_set_tag(v___x_1567_, 1);
                    lean_ctor_set(v___x_1567_, 1, v___x_1571_);
                    lean_ctor_set(v___x_1567_, 0, v___x_1570_);
                    v___x_1573_ = v___x_1567_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1570_);
                    lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1571_);
                    v___x_1573_ = v_reuseFailAlloc_1587_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1574_ = l_Lean_instReprDataValue_repr(v_snd_1565_, v___x_1569_);
                v___x_1575_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                lean_ctor_set(v___x_1575_, 1, v___x_1573_);
                v___x_1576_ = l_List_reverse___redArg(v___x_1575_);
                v___x_1577_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3;
                v___x_1578_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0_spec__2(v___x_1576_, v___x_1577_);
                v___x_1579_ = lean_obj_once(core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6), core::ptr::addr_of_mut!(l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6_once), _init_l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__6);
                v___x_1580_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__7;
                v___x_1581_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1581_, 0, v___x_1580_);
                lean_ctor_set(v___x_1581_, 1, v___x_1578_);
                v___x_1582_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__8;
                v___x_1583_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1583_, 0, v___x_1581_);
                lean_ctor_set(v___x_1583_, 1, v___x_1582_);
                v___x_1584_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1584_, 0, v___x_1579_);
                lean_ctor_set(v___x_1584_, 1, v___x_1583_);
                v___x_1585_ = 0;
                v___x_1586_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1586_, 0, v___x_1584_);
                lean_ctor_set_uint8(
                    v___x_1586_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1585_,
                );
                return v___x_1586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(
    mut v_x_1589_: *mut LeanObject,
    mut v_x_1590_: *mut LeanObject,
    mut v_x_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1591_) == 0 {
                    lean_dec(v_x_1589_);
                    return v_x_1590_;
                } else {
                    v_head_1592_ = lean_ctor_get(v_x_1591_, 0);
                    v_tail_1593_ = lean_ctor_get(v_x_1591_, 1);
                    v_isSharedCheck_1603_ = (!lean_is_exclusive(v_x_1591_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1595_ = v_x_1591_;
                        v_isShared_1596_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1593_);
                        lean_inc(v_head_1592_);
                        lean_dec(v_x_1591_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1589_);
                if v_isShared_1596_ == 0 {
                    lean_ctor_set_tag(v___x_1595_, 5);
                    lean_ctor_set(v___x_1595_, 1, v_x_1589_);
                    lean_ctor_set(v___x_1595_, 0, v_x_1590_);
                    v___x_1598_ = v___x_1595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_x_1590_);
                    lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_x_1589_);
                    v___x_1598_ = v_reuseFailAlloc_1602_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1599_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1592_);
                v___x_1600_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1600_, 0, v___x_1598_);
                lean_ctor_set(v___x_1600_, 1, v___x_1599_);
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
    mut v_x_1604_: *mut LeanObject,
    mut v_x_1605_: *mut LeanObject,
    mut v_x_1606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1611_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1606_) == 0 {
                    lean_dec(v_x_1604_);
                    return v_x_1605_;
                } else {
                    v_head_1607_ = lean_ctor_get(v_x_1606_, 0);
                    v_tail_1608_ = lean_ctor_get(v_x_1606_, 1);
                    v_isSharedCheck_1618_ = (!lean_is_exclusive(v_x_1606_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v___x_1610_ = v_x_1606_;
                        v_isShared_1611_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1608_);
                        lean_inc(v_head_1607_);
                        lean_dec(v_x_1606_);
                        v___x_1610_ = lean_box(0);
                        v_isShared_1611_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_x_1604_);
                if v_isShared_1611_ == 0 {
                    lean_ctor_set_tag(v___x_1610_, 5);
                    lean_ctor_set(v___x_1610_, 1, v_x_1604_);
                    lean_ctor_set(v___x_1610_, 0, v_x_1605_);
                    v___x_1613_ = v___x_1610_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_x_1605_);
                    lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_x_1604_);
                    v___x_1613_ = v_reuseFailAlloc_1617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1614_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1607_);
                v___x_1615_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_1615_, 0, v___x_1613_);
                lean_ctor_set(v___x_1615_, 1, v___x_1614_);
                v___x_1616_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4_spec__6(v_x_1604_, v___x_1615_, v_tail_1608_);
                return v___x_1616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(
    mut v_x_1619_: *mut LeanObject,
    mut v_x_1620_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1619_) == 0 {
        let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_1620_);
        v___x_1621_ = lean_box(0);
        return v___x_1621_;
    } else {
        let mut v_tail_1622_: *mut LeanObject = core::ptr::null_mut();
        v_tail_1622_ = lean_ctor_get(v_x_1619_, 1);
        if lean_obj_tag(v_tail_1622_) == 0 {
            let mut v_head_1623_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_x_1620_);
            v_head_1623_ = lean_ctor_get(v_x_1619_, 0);
            lean_inc(v_head_1623_);
            lean_dec_ref_known(v_x_1619_, 2);
            v___x_1624_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1623_);
            return v___x_1624_;
        } else {
            let mut v_head_1625_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_1622_);
            v_head_1625_ = lean_ctor_get(v_x_1619_, 0);
            lean_inc(v_head_1625_);
            lean_dec_ref_known(v_x_1619_, 2);
            v___x_1626_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(v_head_1625_);
            v___x_1627_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1_spec__4(v_x_1620_, v___x_1626_, v_tail_1622_);
            return v___x_1627_;
        }
    }
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__2;
    v___x_1634_ = lean_string_length(v___x_1633_);
    return v___x_1634_;
}
pub unsafe fn _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = lean_obj_once(
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
    mut v_a_1641_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_1641_) == 0 {
        let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
        v___x_1642_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__1;
        return v___x_1642_;
    } else {
        let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1651_: u8 = 0;
        let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
        v___x_1643_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg___closed__3;
        v___x_1644_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__1(v_a_1641_, v___x_1643_);
        v___x_1645_ = lean_obj_once(
            core::ptr::addr_of_mut!(
                l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5
            ),
            core::ptr::addr_of_mut!(
                l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5_once
            ),
            _init_l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__5,
        );
        v___x_1646_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__6;
        v___x_1647_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1647_, 0, v___x_1646_);
        lean_ctor_set(v___x_1647_, 1, v___x_1644_);
        v___x_1648_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg___closed__7;
        v___x_1649_ = lean_alloc_ctor(5, 2, (0) as u32);
        lean_ctor_set(v___x_1649_, 0, v___x_1647_);
        lean_ctor_set(v___x_1649_, 1, v___x_1648_);
        v___x_1650_ = lean_alloc_ctor(4, 2, (0) as u32);
        lean_ctor_set(v___x_1650_, 0, v___x_1645_);
        lean_ctor_set(v___x_1650_, 1, v___x_1649_);
        v___x_1651_ = 0;
        v___x_1652_ = lean_alloc_ctor(6, 1, (1) as u32);
        lean_ctor_set(v___x_1652_, 0, v___x_1650_);
        lean_ctor_set_uint8(
            v___x_1652_,
            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
            v___x_1651_,
        );
        return v___x_1652_;
    }
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__7() -> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = lean_unsigned_to_nat(11);
    v___x_1667_ = lean_nat_to_int(v___x_1666_);
    return v___x_1667_;
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lean_instReprKVMap_repr___redArg___closed__0;
    v___x_1670_ = lean_string_length(v___x_1669_);
    return v___x_1670_;
}
pub unsafe fn _init_l_Lean_instReprKVMap_repr___redArg___closed__10() -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__9),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__9_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__9,
    );
    v___x_1672_ = lean_nat_to_int(v___x_1671_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_instReprKVMap_repr___redArg(
    mut v_x_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: u8 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lean_instReprKVMap_repr___redArg___closed__6;
    v___x_1679_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__7),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__7_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__7,
    );
    v___x_1680_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_x_1677_);
    v___x_1681_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1681_, 0, v___x_1679_);
    lean_ctor_set(v___x_1681_, 1, v___x_1680_);
    v___x_1682_ = 0;
    v___x_1683_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1683_, 0, v___x_1681_);
    lean_ctor_set_uint8(
        v___x_1683_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1682_,
    );
    v___x_1684_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1684_, 0, v___x_1678_);
    lean_ctor_set(v___x_1684_, 1, v___x_1683_);
    v___x_1685_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__10),
        core::ptr::addr_of_mut!(l_Lean_instReprKVMap_repr___redArg___closed__10_once),
        _init_l_Lean_instReprKVMap_repr___redArg___closed__10,
    );
    v___x_1686_ = l_Lean_instReprKVMap_repr___redArg___closed__11;
    v___x_1687_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1687_, 0, v___x_1686_);
    lean_ctor_set(v___x_1687_, 1, v___x_1684_);
    v___x_1688_ = l_Lean_instReprKVMap_repr___redArg___closed__12;
    v___x_1689_ = lean_alloc_ctor(5, 2, (0) as u32);
    lean_ctor_set(v___x_1689_, 0, v___x_1687_);
    lean_ctor_set(v___x_1689_, 1, v___x_1688_);
    v___x_1690_ = lean_alloc_ctor(4, 2, (0) as u32);
    lean_ctor_set(v___x_1690_, 0, v___x_1685_);
    lean_ctor_set(v___x_1690_, 1, v___x_1689_);
    v___x_1691_ = lean_alloc_ctor(6, 1, (1) as u32);
    lean_ctor_set(v___x_1691_, 0, v___x_1690_);
    lean_ctor_set_uint8(
        v___x_1691_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_1682_,
    );
    return v___x_1691_;
}
pub unsafe fn l_Lean_instReprKVMap_repr(
    mut v_x_1692_: *mut LeanObject,
    mut v_prec_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    v___x_1694_ = l_Lean_instReprKVMap_repr___redArg(v_x_1692_);
    return v___x_1694_;
}
pub unsafe fn l_Lean_instReprKVMap_repr___boxed(
    mut v_x_1695_: *mut LeanObject,
    mut v_prec_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1697_: *mut LeanObject = core::ptr::null_mut();
    v_res_1697_ = l_Lean_instReprKVMap_repr(v_x_1695_, v_prec_1696_);
    lean_dec(v_prec_1696_);
    return v_res_1697_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(
    mut v_a_1698_: *mut LeanObject,
    mut v_n_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    v___x_1700_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___redArg(v_a_1698_);
    return v___x_1700_;
}
pub unsafe fn l_List_repr___at___00Lean_instReprKVMap_repr_spec__0___boxed(
    mut v_a_1701_: *mut LeanObject,
    mut v_n_1702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1703_: *mut LeanObject = core::ptr::null_mut();
    v_res_1703_ = l_List_repr___at___00Lean_instReprKVMap_repr_spec__0(v_a_1701_, v_n_1702_);
    lean_dec(v_n_1702_);
    return v_res_1703_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(
    mut v_x_1704_: *mut LeanObject,
    mut v_x_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ =
        l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___redArg(
            v_x_1704_,
        );
    return v___x_1706_;
}
pub unsafe fn l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0___boxed(
    mut v_x_1707_: *mut LeanObject,
    mut v_x_1708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1709_: *mut LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Prod_repr___at___00List_repr___at___00Lean_instReprKVMap_repr_spec__0_spec__0(
        v_x_1707_, v_x_1708_,
    );
    lean_dec(v_x_1708_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_KVMap_instToString___lam__0(
    mut v___f_1712_: *mut LeanObject,
    mut v_m_1713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_List_toString___redArg(v___f_1712_, v_m_1713_);
    return v___x_1714_;
}
pub unsafe fn _init_l_Lean_KVMap_empty() -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1722_ = lean_box(0);
    return v___x_1722_;
}
pub unsafe fn l_Lean_KVMap_isEmpty(mut v_x_1723_: *mut LeanObject) -> u8 {
    let mut v___x_1724_: u8 = 0;
    v___x_1724_ = l_List_isEmpty___redArg(v_x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_KVMap_isEmpty___boxed(mut v_x_1725_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1726_: u8 = 0;
    let mut v_r_1727_: *mut LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_KVMap_isEmpty(v_x_1725_);
    lean_dec(v_x_1725_);
    v_r_1727_ = lean_box((v_res_1726_) as usize);
    return v_r_1727_;
}
pub unsafe fn l_Lean_KVMap_size(mut v_m_1728_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    v___x_1729_ = l_List_lengthTR___redArg(v_m_1728_);
    return v___x_1729_;
}
pub unsafe fn l_Lean_KVMap_size___boxed(mut v_m_1730_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1731_: *mut LeanObject = core::ptr::null_mut();
    v_res_1731_ = l_Lean_KVMap_size(v_m_1730_);
    lean_dec(v_m_1730_);
    return v_res_1731_;
}
pub unsafe fn l_Lean_KVMap_findCore(
    mut v_x_1732_: *mut LeanObject,
    mut v_x_1733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1732_) == 0 {
                    v___x_1734_ = lean_box(0);
                    return v___x_1734_;
                } else {
                    v_head_1735_ = lean_ctor_get(v_x_1732_, 0);
                    v_tail_1736_ = lean_ctor_get(v_x_1732_, 1);
                    v_fst_1737_ = lean_ctor_get(v_head_1735_, 0);
                    v_snd_1738_ = lean_ctor_get(v_head_1735_, 1);
                    v___x_1739_ = lean_name_eq(v_fst_1737_, v_x_1733_);
                    if v___x_1739_ == 0 {
                        v_x_1732_ = v_tail_1736_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_snd_1738_);
                        v___x_1741_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1741_, 0, v_snd_1738_);
                        return v___x_1741_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_findCore___boxed(
    mut v_x_1742_: *mut LeanObject,
    mut v_x_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1744_: *mut LeanObject = core::ptr::null_mut();
    v_res_1744_ = l_Lean_KVMap_findCore(v_x_1742_, v_x_1743_);
    lean_dec(v_x_1743_);
    lean_dec(v_x_1742_);
    return v_res_1744_;
}
pub unsafe fn l_Lean_KVMap_find(
    mut v_x_1745_: *mut LeanObject,
    mut v_x_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    v___x_1747_ = l_Lean_KVMap_findCore(v_x_1745_, v_x_1746_);
    return v___x_1747_;
}
pub unsafe fn l_Lean_KVMap_find___boxed(
    mut v_x_1748_: *mut LeanObject,
    mut v_x_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_KVMap_find(v_x_1748_, v_x_1749_);
    lean_dec(v_x_1749_);
    lean_dec(v_x_1748_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_KVMap_findD(
    mut v_m_1751_: *mut LeanObject,
    mut v_k_1752_: *mut LeanObject,
    mut v_d_u2080_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1754_ = l_Lean_KVMap_findCore(v_m_1751_, v_k_1752_);
    if lean_obj_tag(v___x_1754_) == 0 {
        lean_inc_ref(v_d_u2080_1753_);
        return v_d_u2080_1753_;
    } else {
        let mut v_val_1755_: *mut LeanObject = core::ptr::null_mut();
        v_val_1755_ = lean_ctor_get(v___x_1754_, 0);
        lean_inc(v_val_1755_);
        lean_dec_ref_known(v___x_1754_, 1);
        return v_val_1755_;
    }
}
pub unsafe fn l_Lean_KVMap_findD___boxed(
    mut v_m_1756_: *mut LeanObject,
    mut v_k_1757_: *mut LeanObject,
    mut v_d_u2080_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1759_: *mut LeanObject = core::ptr::null_mut();
    v_res_1759_ = l_Lean_KVMap_findD(v_m_1756_, v_k_1757_, v_d_u2080_1758_);
    lean_dec_ref(v_d_u2080_1758_);
    lean_dec(v_k_1757_);
    lean_dec(v_m_1756_);
    return v_res_1759_;
}
pub unsafe fn l_Lean_KVMap_insertCore(
    mut v_x_1760_: *mut LeanObject,
    mut v_x_1761_: *mut LeanObject,
    mut v_x_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v_fst_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1778_: u8 = 0;
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1785_: u8 = 0;
    let mut v_unused_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1788_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1760_) == 0 {
                    v___x_1763_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1763_, 0, v_x_1761_);
                    lean_ctor_set(v___x_1763_, 1, v_x_1762_);
                    v___x_1764_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1764_, 0, v___x_1763_);
                    lean_ctor_set(v___x_1764_, 1, v_x_1760_);
                    return v___x_1764_;
                } else {
                    v_head_1765_ = lean_ctor_get(v_x_1760_, 0);
                    v_tail_1766_ = lean_ctor_get(v_x_1760_, 1);
                    v_isSharedCheck_1788_ = (!lean_is_exclusive(v_x_1760_)) as u8;
                    if v_isSharedCheck_1788_ == 0 {
                        v___x_1768_ = v_x_1760_;
                        v_isShared_1769_ = v_isSharedCheck_1788_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1766_);
                        lean_inc(v_head_1765_);
                        lean_dec(v_x_1760_);
                        v___x_1768_ = lean_box(0);
                        v_isShared_1769_ = v_isSharedCheck_1788_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1770_ = lean_ctor_get(v_head_1765_, 0);
                v___x_1771_ = lean_name_eq(v_fst_1770_, v_x_1761_);
                if v___x_1771_ == 0 {
                    v___x_1772_ = l_Lean_KVMap_insertCore(v_tail_1766_, v_x_1761_, v_x_1762_);
                    if v_isShared_1769_ == 0 {
                        lean_ctor_set(v___x_1768_, 1, v___x_1772_);
                        v___x_1774_ = v___x_1768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_head_1765_);
                        lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1772_);
                        v___x_1774_ = v_reuseFailAlloc_1775_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_fst_1770_);
                    lean_dec(v_x_1761_);
                    v_isSharedCheck_1785_ = (!lean_is_exclusive(v_head_1765_)) as u8;
                    if v_isSharedCheck_1785_ == 0 {
                        v_unused_1786_ = lean_ctor_get(v_head_1765_, 1);
                        lean_dec(v_unused_1786_);
                        v_unused_1787_ = lean_ctor_get(v_head_1765_, 0);
                        lean_dec(v_unused_1787_);
                        v___x_1777_ = v_head_1765_;
                        v_isShared_1778_ = v_isSharedCheck_1785_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_head_1765_);
                        v___x_1777_ = lean_box(0);
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
                    lean_ctor_set(v___x_1777_, 1, v_x_1762_);
                    v___x_1780_ = v___x_1777_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_fst_1770_);
                    lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_x_1762_);
                    v___x_1780_ = v_reuseFailAlloc_1784_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1769_ == 0 {
                    lean_ctor_set(v___x_1768_, 0, v___x_1780_);
                    v___x_1782_ = v___x_1768_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_tail_1766_);
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
    mut v_x_1789_: *mut LeanObject,
    mut v_x_1790_: *mut LeanObject,
    mut v_x_1791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    v___x_1792_ = l_Lean_KVMap_insertCore(v_x_1789_, v_x_1790_, v_x_1791_);
    return v___x_1792_;
}
pub unsafe fn l_Lean_KVMap_contains(
    mut v_m_1793_: *mut LeanObject,
    mut v_n_1794_: *mut LeanObject,
) -> u8 {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_KVMap_findCore(v_m_1793_, v_n_1794_);
    if lean_obj_tag(v___x_1795_) == 0 {
        let mut v___x_1796_: u8 = 0;
        v___x_1796_ = 0;
        return v___x_1796_;
    } else {
        let mut v___x_1797_: u8 = 0;
        lean_dec_ref_known(v___x_1795_, 1);
        v___x_1797_ = 1;
        return v___x_1797_;
    }
}
pub unsafe fn l_Lean_KVMap_contains___boxed(
    mut v_m_1798_: *mut LeanObject,
    mut v_n_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1800_: u8 = 0;
    let mut v_r_1801_: *mut LeanObject = core::ptr::null_mut();
    v_res_1800_ = l_Lean_KVMap_contains(v_m_1798_, v_n_1799_);
    lean_dec(v_n_1799_);
    lean_dec(v_m_1798_);
    v_r_1801_ = lean_box((v_res_1800_) as usize);
    return v_r_1801_;
}
pub unsafe fn l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(
    mut v_x_1802_: *mut LeanObject,
    mut v_a_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1810_: u8 = 0;
    let mut v_fst_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1803_) == 0 {
                    v___x_1805_ = l_List_reverse___redArg(v_a_1804_);
                    return v___x_1805_;
                } else {
                    v_head_1806_ = lean_ctor_get(v_a_1803_, 0);
                    v_tail_1807_ = lean_ctor_get(v_a_1803_, 1);
                    v_isSharedCheck_1818_ = (!lean_is_exclusive(v_a_1803_)) as u8;
                    if v_isSharedCheck_1818_ == 0 {
                        v___x_1809_ = v_a_1803_;
                        v_isShared_1810_ = v_isSharedCheck_1818_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1807_);
                        lean_inc(v_head_1806_);
                        lean_dec(v_a_1803_);
                        v___x_1809_ = lean_box(0);
                        v_isShared_1810_ = v_isSharedCheck_1818_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1811_ = lean_ctor_get(v_head_1806_, 0);
                v___x_1812_ = lean_name_eq(v_fst_1811_, v_x_1802_);
                if v___x_1812_ == 0 {
                    if v_isShared_1810_ == 0 {
                        lean_ctor_set(v___x_1809_, 1, v_a_1804_);
                        v___x_1814_ = v___x_1809_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1816_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1816_, 0, v_head_1806_);
                        lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_a_1804_);
                        v___x_1814_ = v_reuseFailAlloc_1816_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1809_);
                    lean_dec(v_head_1806_);
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
    mut v_x_1819_: *mut LeanObject,
    mut v_a_1820_: *mut LeanObject,
    mut v_a_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1822_: *mut LeanObject = core::ptr::null_mut();
    v_res_1822_ =
        l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_1819_, v_a_1820_, v_a_1821_);
    lean_dec(v_x_1819_);
    return v_res_1822_;
}
pub unsafe fn l_Lean_KVMap_erase(
    mut v_x_1823_: *mut LeanObject,
    mut v_x_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    v___x_1825_ = lean_box(0);
    v___x_1826_ =
        l_List_filterTR_loop___at___00Lean_KVMap_erase_spec__0(v_x_1824_, v_x_1823_, v___x_1825_);
    return v___x_1826_;
}
pub unsafe fn l_Lean_KVMap_erase___boxed(
    mut v_x_1827_: *mut LeanObject,
    mut v_x_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1829_: *mut LeanObject = core::ptr::null_mut();
    v_res_1829_ = l_Lean_KVMap_erase(v_x_1827_, v_x_1828_);
    lean_dec(v_x_1828_);
    return v_res_1829_;
}
pub unsafe fn l_Lean_KVMap_getString(
    mut v_m_1830_: *mut LeanObject,
    mut v_k_1831_: *mut LeanObject,
    mut v_defVal_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    v___x_1833_ = l_Lean_KVMap_findCore(v_m_1830_, v_k_1831_);
    if lean_obj_tag(v___x_1833_) == 1 {
        let mut v_val_1834_: *mut LeanObject = core::ptr::null_mut();
        v_val_1834_ = lean_ctor_get(v___x_1833_, 0);
        lean_inc(v_val_1834_);
        lean_dec_ref_known(v___x_1833_, 1);
        if lean_obj_tag(v_val_1834_) == 0 {
            let mut v_v_1835_: *mut LeanObject = core::ptr::null_mut();
            v_v_1835_ = lean_ctor_get(v_val_1834_, 0);
            lean_inc_ref(v_v_1835_);
            lean_dec_ref_known(v_val_1834_, 1);
            return v_v_1835_;
        } else {
            lean_dec(v_val_1834_);
            lean_inc_ref(v_defVal_1832_);
            return v_defVal_1832_;
        }
    } else {
        lean_dec(v___x_1833_);
        lean_inc_ref(v_defVal_1832_);
        return v_defVal_1832_;
    }
}
pub unsafe fn l_Lean_KVMap_getString___boxed(
    mut v_m_1836_: *mut LeanObject,
    mut v_k_1837_: *mut LeanObject,
    mut v_defVal_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
    v_res_1839_ = l_Lean_KVMap_getString(v_m_1836_, v_k_1837_, v_defVal_1838_);
    lean_dec_ref(v_defVal_1838_);
    lean_dec(v_k_1837_);
    lean_dec(v_m_1836_);
    return v_res_1839_;
}
pub unsafe fn l_Lean_KVMap_getNat(
    mut v_m_1840_: *mut LeanObject,
    mut v_k_1841_: *mut LeanObject,
    mut v_defVal_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Lean_KVMap_findCore(v_m_1840_, v_k_1841_);
    if lean_obj_tag(v___x_1843_) == 1 {
        let mut v_val_1844_: *mut LeanObject = core::ptr::null_mut();
        v_val_1844_ = lean_ctor_get(v___x_1843_, 0);
        lean_inc(v_val_1844_);
        lean_dec_ref_known(v___x_1843_, 1);
        if lean_obj_tag(v_val_1844_) == 3 {
            let mut v_v_1845_: *mut LeanObject = core::ptr::null_mut();
            v_v_1845_ = lean_ctor_get(v_val_1844_, 0);
            lean_inc(v_v_1845_);
            lean_dec_ref_known(v_val_1844_, 1);
            return v_v_1845_;
        } else {
            lean_dec(v_val_1844_);
            lean_inc(v_defVal_1842_);
            return v_defVal_1842_;
        }
    } else {
        lean_dec(v___x_1843_);
        lean_inc(v_defVal_1842_);
        return v_defVal_1842_;
    }
}
pub unsafe fn l_Lean_KVMap_getNat___boxed(
    mut v_m_1846_: *mut LeanObject,
    mut v_k_1847_: *mut LeanObject,
    mut v_defVal_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1849_: *mut LeanObject = core::ptr::null_mut();
    v_res_1849_ = l_Lean_KVMap_getNat(v_m_1846_, v_k_1847_, v_defVal_1848_);
    lean_dec(v_defVal_1848_);
    lean_dec(v_k_1847_);
    lean_dec(v_m_1846_);
    return v_res_1849_;
}
pub unsafe fn l_Lean_KVMap_getInt(
    mut v_m_1850_: *mut LeanObject,
    mut v_k_1851_: *mut LeanObject,
    mut v_defVal_1852_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    v___x_1853_ = l_Lean_KVMap_findCore(v_m_1850_, v_k_1851_);
    if lean_obj_tag(v___x_1853_) == 1 {
        let mut v_val_1854_: *mut LeanObject = core::ptr::null_mut();
        v_val_1854_ = lean_ctor_get(v___x_1853_, 0);
        lean_inc(v_val_1854_);
        lean_dec_ref_known(v___x_1853_, 1);
        if lean_obj_tag(v_val_1854_) == 4 {
            let mut v_v_1855_: *mut LeanObject = core::ptr::null_mut();
            v_v_1855_ = lean_ctor_get(v_val_1854_, 0);
            lean_inc(v_v_1855_);
            lean_dec_ref_known(v_val_1854_, 1);
            return v_v_1855_;
        } else {
            lean_dec(v_val_1854_);
            lean_inc(v_defVal_1852_);
            return v_defVal_1852_;
        }
    } else {
        lean_dec(v___x_1853_);
        lean_inc(v_defVal_1852_);
        return v_defVal_1852_;
    }
}
pub unsafe fn l_Lean_KVMap_getInt___boxed(
    mut v_m_1856_: *mut LeanObject,
    mut v_k_1857_: *mut LeanObject,
    mut v_defVal_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1859_: *mut LeanObject = core::ptr::null_mut();
    v_res_1859_ = l_Lean_KVMap_getInt(v_m_1856_, v_k_1857_, v_defVal_1858_);
    lean_dec(v_defVal_1858_);
    lean_dec(v_k_1857_);
    lean_dec(v_m_1856_);
    return v_res_1859_;
}
pub unsafe fn l_Lean_KVMap_getBool(
    mut v_m_1860_: *mut LeanObject,
    mut v_k_1861_: *mut LeanObject,
    mut v_defVal_1862_: u8,
) -> u8 {
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    v___x_1863_ = l_Lean_KVMap_findCore(v_m_1860_, v_k_1861_);
    if lean_obj_tag(v___x_1863_) == 1 {
        let mut v_val_1864_: *mut LeanObject = core::ptr::null_mut();
        v_val_1864_ = lean_ctor_get(v___x_1863_, 0);
        lean_inc(v_val_1864_);
        lean_dec_ref_known(v___x_1863_, 1);
        if lean_obj_tag(v_val_1864_) == 1 {
            let mut v_v_1865_: u8 = 0;
            v_v_1865_ = lean_ctor_get_uint8(v_val_1864_, 0 as u32);
            lean_dec_ref_known(v_val_1864_, 0);
            return v_v_1865_;
        } else {
            lean_dec(v_val_1864_);
            return v_defVal_1862_;
        }
    } else {
        lean_dec(v___x_1863_);
        return v_defVal_1862_;
    }
}
pub unsafe fn l_Lean_KVMap_getBool___boxed(
    mut v_m_1866_: *mut LeanObject,
    mut v_k_1867_: *mut LeanObject,
    mut v_defVal_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defVal_boxed_1869_: u8 = 0;
    let mut v_res_1870_: u8 = 0;
    let mut v_r_1871_: *mut LeanObject = core::ptr::null_mut();
    v_defVal_boxed_1869_ = (lean_unbox(v_defVal_1868_) as u8);
    v_res_1870_ = l_Lean_KVMap_getBool(v_m_1866_, v_k_1867_, v_defVal_boxed_1869_);
    lean_dec(v_k_1867_);
    lean_dec(v_m_1866_);
    v_r_1871_ = lean_box((v_res_1870_) as usize);
    return v_r_1871_;
}
pub unsafe fn l_Lean_KVMap_getName(
    mut v_m_1872_: *mut LeanObject,
    mut v_k_1873_: *mut LeanObject,
    mut v_defVal_1874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Lean_KVMap_findCore(v_m_1872_, v_k_1873_);
    if lean_obj_tag(v___x_1875_) == 1 {
        let mut v_val_1876_: *mut LeanObject = core::ptr::null_mut();
        v_val_1876_ = lean_ctor_get(v___x_1875_, 0);
        lean_inc(v_val_1876_);
        lean_dec_ref_known(v___x_1875_, 1);
        if lean_obj_tag(v_val_1876_) == 2 {
            let mut v_v_1877_: *mut LeanObject = core::ptr::null_mut();
            v_v_1877_ = lean_ctor_get(v_val_1876_, 0);
            lean_inc(v_v_1877_);
            lean_dec_ref_known(v_val_1876_, 1);
            return v_v_1877_;
        } else {
            lean_dec(v_val_1876_);
            lean_inc(v_defVal_1874_);
            return v_defVal_1874_;
        }
    } else {
        lean_dec(v___x_1875_);
        lean_inc(v_defVal_1874_);
        return v_defVal_1874_;
    }
}
pub unsafe fn l_Lean_KVMap_getName___boxed(
    mut v_m_1878_: *mut LeanObject,
    mut v_k_1879_: *mut LeanObject,
    mut v_defVal_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1881_: *mut LeanObject = core::ptr::null_mut();
    v_res_1881_ = l_Lean_KVMap_getName(v_m_1878_, v_k_1879_, v_defVal_1880_);
    lean_dec(v_defVal_1880_);
    lean_dec(v_k_1879_);
    lean_dec(v_m_1878_);
    return v_res_1881_;
}
pub unsafe fn l_Lean_KVMap_getSyntax(
    mut v_m_1882_: *mut LeanObject,
    mut v_k_1883_: *mut LeanObject,
    mut v_defVal_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_KVMap_findCore(v_m_1882_, v_k_1883_);
    if lean_obj_tag(v___x_1885_) == 1 {
        let mut v_val_1886_: *mut LeanObject = core::ptr::null_mut();
        v_val_1886_ = lean_ctor_get(v___x_1885_, 0);
        lean_inc(v_val_1886_);
        lean_dec_ref_known(v___x_1885_, 1);
        if lean_obj_tag(v_val_1886_) == 5 {
            let mut v_v_1887_: *mut LeanObject = core::ptr::null_mut();
            v_v_1887_ = lean_ctor_get(v_val_1886_, 0);
            lean_inc(v_v_1887_);
            lean_dec_ref_known(v_val_1886_, 1);
            return v_v_1887_;
        } else {
            lean_dec(v_val_1886_);
            lean_inc(v_defVal_1884_);
            return v_defVal_1884_;
        }
    } else {
        lean_dec(v___x_1885_);
        lean_inc(v_defVal_1884_);
        return v_defVal_1884_;
    }
}
pub unsafe fn l_Lean_KVMap_getSyntax___boxed(
    mut v_m_1888_: *mut LeanObject,
    mut v_k_1889_: *mut LeanObject,
    mut v_defVal_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lean_KVMap_getSyntax(v_m_1888_, v_k_1889_, v_defVal_1890_);
    lean_dec(v_defVal_1890_);
    lean_dec(v_k_1889_);
    lean_dec(v_m_1888_);
    return v_res_1891_;
}
pub unsafe fn l_Lean_KVMap_setString(
    mut v_m_1892_: *mut LeanObject,
    mut v_k_1893_: *mut LeanObject,
    mut v_v_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    v___x_1895_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1895_, 0, v_v_1894_);
    v___x_1896_ = l_Lean_KVMap_insertCore(v_m_1892_, v_k_1893_, v___x_1895_);
    return v___x_1896_;
}
pub unsafe fn l_Lean_KVMap_setNat(
    mut v_m_1897_: *mut LeanObject,
    mut v_k_1898_: *mut LeanObject,
    mut v_v_1899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    v___x_1900_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1900_, 0, v_v_1899_);
    v___x_1901_ = l_Lean_KVMap_insertCore(v_m_1897_, v_k_1898_, v___x_1900_);
    return v___x_1901_;
}
pub unsafe fn l_Lean_KVMap_setInt(
    mut v_m_1902_: *mut LeanObject,
    mut v_k_1903_: *mut LeanObject,
    mut v_v_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1905_, 0, v_v_1904_);
    v___x_1906_ = l_Lean_KVMap_insertCore(v_m_1902_, v_k_1903_, v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn l_Lean_KVMap_setBool(
    mut v_m_1907_: *mut LeanObject,
    mut v_k_1908_: *mut LeanObject,
    mut v_v_1909_: u8,
) -> *mut LeanObject {
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    v___x_1910_ = lean_alloc_ctor(1, 0, (1) as u32);
    lean_ctor_set_uint8(v___x_1910_, 0 as u32, v_v_1909_);
    v___x_1911_ = l_Lean_KVMap_insertCore(v_m_1907_, v_k_1908_, v___x_1910_);
    return v___x_1911_;
}
pub unsafe fn l_Lean_KVMap_setBool___boxed(
    mut v_m_1912_: *mut LeanObject,
    mut v_k_1913_: *mut LeanObject,
    mut v_v_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_boxed_1915_: u8 = 0;
    let mut v_res_1916_: *mut LeanObject = core::ptr::null_mut();
    v_v_boxed_1915_ = (lean_unbox(v_v_1914_) as u8);
    v_res_1916_ = l_Lean_KVMap_setBool(v_m_1912_, v_k_1913_, v_v_boxed_1915_);
    return v_res_1916_;
}
pub unsafe fn l_Lean_KVMap_setName(
    mut v_m_1917_: *mut LeanObject,
    mut v_k_1918_: *mut LeanObject,
    mut v_v_1919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    v___x_1920_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v_v_1919_);
    v___x_1921_ = l_Lean_KVMap_insertCore(v_m_1917_, v_k_1918_, v___x_1920_);
    return v___x_1921_;
}
pub unsafe fn l_Lean_KVMap_setSyntax(
    mut v_m_1922_: *mut LeanObject,
    mut v_k_1923_: *mut LeanObject,
    mut v_v_1924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    v___x_1925_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_1925_, 0, v_v_1924_);
    v___x_1926_ = l_Lean_KVMap_insertCore(v_m_1922_, v_k_1923_, v___x_1925_);
    return v___x_1926_;
}
pub unsafe fn l_Lean_KVMap_updateString(
    mut v_m_1927_: *mut LeanObject,
    mut v_k_1928_: *mut LeanObject,
    mut v_f_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l_Lean_instInhabitedDataValue_default___closed__0;
    v___x_1931_ = l_Lean_KVMap_getString(v_m_1927_, v_k_1928_, v___x_1930_);
    v___x_1932_ = lean_apply_1(v_f_1929_, v___x_1931_);
    v___x_1933_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1933_, 0, v___x_1932_);
    v___x_1934_ = l_Lean_KVMap_insertCore(v_m_1927_, v_k_1928_, v___x_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lean_KVMap_updateNat(
    mut v_m_1935_: *mut LeanObject,
    mut v_k_1936_: *mut LeanObject,
    mut v_f_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    v___x_1938_ = lean_unsigned_to_nat(0);
    v___x_1939_ = l_Lean_KVMap_getNat(v_m_1935_, v_k_1936_, v___x_1938_);
    v___x_1940_ = lean_apply_1(v_f_1937_, v___x_1939_);
    v___x_1941_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1941_, 0, v___x_1940_);
    v___x_1942_ = l_Lean_KVMap_insertCore(v_m_1935_, v_k_1936_, v___x_1941_);
    return v___x_1942_;
}
pub unsafe fn l_Lean_KVMap_updateInt(
    mut v_m_1943_: *mut LeanObject,
    mut v_k_1944_: *mut LeanObject,
    mut v_f_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    v___x_1946_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17),
        core::ptr::addr_of_mut!(l_Lean_instReprDataValue_repr___closed__17_once),
        _init_l_Lean_instReprDataValue_repr___closed__17,
    );
    v___x_1947_ = l_Lean_KVMap_getInt(v_m_1943_, v_k_1944_, v___x_1946_);
    v___x_1948_ = lean_apply_1(v_f_1945_, v___x_1947_);
    v___x_1949_ = lean_alloc_ctor(4, 1, (0) as u32);
    lean_ctor_set(v___x_1949_, 0, v___x_1948_);
    v___x_1950_ = l_Lean_KVMap_insertCore(v_m_1943_, v_k_1944_, v___x_1949_);
    return v___x_1950_;
}
pub unsafe fn l_Lean_KVMap_updateBool(
    mut v_m_1951_: *mut LeanObject,
    mut v_k_1952_: *mut LeanObject,
    mut v_f_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    v___x_1954_ = 0;
    v___x_1955_ = l_Lean_KVMap_getBool(v_m_1951_, v_k_1952_, v___x_1954_);
    v___x_1956_ = lean_box((v___x_1955_) as usize);
    v___x_1957_ = lean_apply_1(v_f_1953_, v___x_1956_);
    v___x_1958_ = lean_alloc_ctor(1, 0, (1) as u32);
    v___x_1959_ = (lean_unbox(v___x_1957_) as u8);
    lean_ctor_set_uint8(v___x_1958_, 0 as u32, v___x_1959_);
    v___x_1960_ = l_Lean_KVMap_insertCore(v_m_1951_, v_k_1952_, v___x_1958_);
    return v___x_1960_;
}
pub unsafe fn l_Lean_KVMap_updateName(
    mut v_m_1961_: *mut LeanObject,
    mut v_k_1962_: *mut LeanObject,
    mut v_f_1963_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v___x_1964_ = lean_box(0);
    v___x_1965_ = l_Lean_KVMap_getName(v_m_1961_, v_k_1962_, v___x_1964_);
    v___x_1966_ = lean_apply_1(v_f_1963_, v___x_1965_);
    v___x_1967_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1967_, 0, v___x_1966_);
    v___x_1968_ = l_Lean_KVMap_insertCore(v_m_1961_, v_k_1962_, v___x_1967_);
    return v___x_1968_;
}
pub unsafe fn l_Lean_KVMap_updateSyntax(
    mut v_m_1969_: *mut LeanObject,
    mut v_k_1970_: *mut LeanObject,
    mut v_f_1971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    v___x_1972_ = lean_box(0);
    v___x_1973_ = l_Lean_KVMap_getSyntax(v_m_1969_, v_k_1970_, v___x_1972_);
    v___x_1974_ = lean_apply_1(v_f_1971_, v___x_1973_);
    v___x_1975_ = lean_alloc_ctor(5, 1, (0) as u32);
    lean_ctor_set(v___x_1975_, 0, v___x_1974_);
    v___x_1976_ = l_Lean_KVMap_insertCore(v_m_1969_, v_k_1970_, v___x_1975_);
    return v___x_1976_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg___lam__0(
    mut v_f_1977_: *mut LeanObject,
    mut v_a_1978_: *mut LeanObject,
    mut v_x_1979_: *mut LeanObject,
    mut v___y_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    v___x_1981_ = lean_apply_2(v_f_1977_, v_a_1978_, v___y_1980_);
    return v___x_1981_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg(
    mut v_inst_1982_: *mut LeanObject,
    mut v_kv_1983_: *mut LeanObject,
    mut v_init_1984_: *mut LeanObject,
    mut v_f_1985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    v___f_1986_ = lean_alloc_closure(
        l_Lean_KVMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1986_, 0, v_f_1985_);
    v___x_1987_ =
        l_List_forIn_x27_loop___redArg(v_inst_1982_, v___f_1986_, v_kv_1983_, v_init_1984_);
    return v___x_1987_;
}
pub unsafe fn l_Lean_KVMap_forIn___redArg___boxed(
    mut v_inst_1988_: *mut LeanObject,
    mut v_kv_1989_: *mut LeanObject,
    mut v_init_1990_: *mut LeanObject,
    mut v_f_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1992_: *mut LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Lean_KVMap_forIn___redArg(v_inst_1988_, v_kv_1989_, v_init_1990_, v_f_1991_);
    lean_dec(v_kv_1989_);
    return v_res_1992_;
}
pub unsafe fn l_Lean_KVMap_forIn(
    mut v_00_u03b4_1993_: *mut LeanObject,
    mut v_m_1994_: *mut LeanObject,
    mut v_inst_1995_: *mut LeanObject,
    mut v_kv_1996_: *mut LeanObject,
    mut v_init_1997_: *mut LeanObject,
    mut v_f_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___f_1999_ = lean_alloc_closure(
        l_Lean_KVMap_forIn___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_1999_, 0, v_f_1998_);
    v___x_2000_ =
        l_List_forIn_x27_loop___redArg(v_inst_1995_, v___f_1999_, v_kv_1996_, v_init_1997_);
    return v___x_2000_;
}
pub unsafe fn l_Lean_KVMap_forIn___boxed(
    mut v_00_u03b4_2001_: *mut LeanObject,
    mut v_m_2002_: *mut LeanObject,
    mut v_inst_2003_: *mut LeanObject,
    mut v_kv_2004_: *mut LeanObject,
    mut v_init_2005_: *mut LeanObject,
    mut v_f_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2007_: *mut LeanObject = core::ptr::null_mut();
    v_res_2007_ = l_Lean_KVMap_forIn(
        v_00_u03b4_2001_,
        v_m_2002_,
        v_inst_2003_,
        v_kv_2004_,
        v_init_2005_,
        v_f_2006_,
    );
    lean_dec(v_kv_2004_);
    return v_res_2007_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0(
    mut v___y_2008_: *mut LeanObject,
    mut v_a_2009_: *mut LeanObject,
    mut v_x_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    v___x_2012_ = lean_apply_2(v___y_2008_, v_a_2009_, v___y_2011_);
    return v___x_2012_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(
    mut v_inst_2013_: *mut LeanObject,
    mut v_00_u03b2_2014_: *mut LeanObject,
    mut v___y_2015_: *mut LeanObject,
    mut v___y_2016_: *mut LeanObject,
    mut v___y_2017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    v___f_2018_ = lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2018_, 0, v___y_2017_);
    v___x_2019_ =
        l_List_forIn_x27_loop___redArg(v_inst_2013_, v___f_2018_, v___y_2015_, v___y_2016_);
    return v___x_2019_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed(
    mut v_inst_2020_: *mut LeanObject,
    mut v_00_u03b2_2021_: *mut LeanObject,
    mut v___y_2022_: *mut LeanObject,
    mut v___y_2023_: *mut LeanObject,
    mut v___y_2024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2025_: *mut LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1(
        v_inst_2020_,
        v_00_u03b2_2021_,
        v___y_2022_,
        v___y_2023_,
        v___y_2024_,
    );
    lean_dec(v___y_2022_);
    return v_res_2025_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg(
    mut v_inst_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2027_: *mut LeanObject = core::ptr::null_mut();
    v___f_2027_ = lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2027_, 0, v_inst_2026_);
    return v___f_2027_;
}
pub unsafe fn l_Lean_KVMap_instForInProdNameDataValueOfMonad(
    mut v_m_2028_: *mut LeanObject,
    mut v_inst_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2030_: *mut LeanObject = core::ptr::null_mut();
    v___f_2030_ = lean_alloc_closure(
        l_Lean_KVMap_instForInProdNameDataValueOfMonad___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_2030_, 0, v_inst_2029_);
    return v___f_2030_;
}
pub unsafe fn l_Lean_KVMap_subsetAux(
    mut v_x_2031_: *mut LeanObject,
    mut v_x_2032_: *mut LeanObject,
) -> u8 {
    let mut v___x_2033_: u8 = 0;
    let mut v_head_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: u8 = 0;
    let mut v_val_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2031_) == 0 {
                    v___x_2033_ = 1;
                    return v___x_2033_;
                } else {
                    v_head_2034_ = lean_ctor_get(v_x_2031_, 0);
                    lean_inc(v_head_2034_);
                    v_tail_2035_ = lean_ctor_get(v_x_2031_, 1);
                    lean_inc(v_tail_2035_);
                    lean_dec_ref_known(v_x_2031_, 2);
                    v_fst_2036_ = lean_ctor_get(v_head_2034_, 0);
                    lean_inc(v_fst_2036_);
                    v_snd_2037_ = lean_ctor_get(v_head_2034_, 1);
                    lean_inc(v_snd_2037_);
                    lean_dec(v_head_2034_);
                    v___x_2038_ = l_Lean_KVMap_findCore(v_x_2032_, v_fst_2036_);
                    lean_dec(v_fst_2036_);
                    if lean_obj_tag(v___x_2038_) == 0 {
                        lean_dec(v_snd_2037_);
                        lean_dec(v_tail_2035_);
                        v___x_2039_ = 0;
                        return v___x_2039_;
                    } else {
                        v_val_2040_ = lean_ctor_get(v___x_2038_, 0);
                        lean_inc(v_val_2040_);
                        lean_dec_ref_known(v___x_2038_, 1);
                        v___x_2041_ = l_Lean_instBEqDataValue_beq(v_snd_2037_, v_val_2040_);
                        if v___x_2041_ == 0 {
                            lean_dec(v_tail_2035_);
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
    mut v_x_2043_: *mut LeanObject,
    mut v_x_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2045_: u8 = 0;
    let mut v_r_2046_: *mut LeanObject = core::ptr::null_mut();
    v_res_2045_ = l_Lean_KVMap_subsetAux(v_x_2043_, v_x_2044_);
    lean_dec(v_x_2044_);
    v_r_2046_ = lean_box((v_res_2045_) as usize);
    return v_r_2046_;
}
pub unsafe fn l_Lean_KVMap_subset(
    mut v_x_2047_: *mut LeanObject,
    mut v_x_2048_: *mut LeanObject,
) -> u8 {
    let mut v___x_2049_: u8 = 0;
    v___x_2049_ = l_Lean_KVMap_subsetAux(v_x_2047_, v_x_2048_);
    return v___x_2049_;
}
pub unsafe fn l_Lean_KVMap_subset___boxed(
    mut v_x_2050_: *mut LeanObject,
    mut v_x_2051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2052_: u8 = 0;
    let mut v_r_2053_: *mut LeanObject = core::ptr::null_mut();
    v_res_2052_ = l_Lean_KVMap_subset(v_x_2050_, v_x_2051_);
    lean_dec(v_x_2051_);
    v_r_2053_ = lean_box((v_res_2052_) as usize);
    return v_r_2053_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
    mut v_mergeFn_2054_: *mut LeanObject,
    mut v_as_x27_2055_: *mut LeanObject,
    mut v_b_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2055_) == 0 {
                    lean_dec_ref(v_mergeFn_2054_);
                    return v_b_2056_;
                } else {
                    v_head_2057_ = lean_ctor_get(v_as_x27_2055_, 0);
                    v_tail_2058_ = lean_ctor_get(v_as_x27_2055_, 1);
                    v_fst_2059_ = lean_ctor_get(v_head_2057_, 0);
                    v_snd_2060_ = lean_ctor_get(v_head_2057_, 1);
                    v___x_2061_ = l_Lean_KVMap_findCore(v_b_2056_, v_fst_2059_);
                    if lean_obj_tag(v___x_2061_) == 1 {
                        v_val_2062_ = lean_ctor_get(v___x_2061_, 0);
                        lean_inc(v_val_2062_);
                        lean_dec_ref_known(v___x_2061_, 1);
                        lean_inc_ref(v_mergeFn_2054_);
                        lean_inc(v_snd_2060_);
                        lean_inc_n(v_fst_2059_, 2);
                        v___x_2063_ =
                            lean_apply_3(v_mergeFn_2054_, v_fst_2059_, v_val_2062_, v_snd_2060_);
                        v___x_2064_ = l_Lean_KVMap_insertCore(v_b_2056_, v_fst_2059_, v___x_2063_);
                        v_as_x27_2055_ = v_tail_2058_;
                        v_b_2056_ = v___x_2064_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_2061_);
                        lean_inc(v_snd_2060_);
                        lean_inc(v_fst_2059_);
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
    mut v_mergeFn_2068_: *mut LeanObject,
    mut v_as_x27_2069_: *mut LeanObject,
    mut v_b_2070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2071_: *mut LeanObject = core::ptr::null_mut();
    v_res_2071_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2068_,
        v_as_x27_2069_,
        v_b_2070_,
    );
    lean_dec(v_as_x27_2069_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_KVMap_mergeBy(
    mut v_mergeFn_2072_: *mut LeanObject,
    mut v_l_2073_: *mut LeanObject,
    mut v_r_2074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2072_,
        v_r_2074_,
        v_l_2073_,
    );
    return v___x_2075_;
}
pub unsafe fn l_Lean_KVMap_mergeBy___boxed(
    mut v_mergeFn_2076_: *mut LeanObject,
    mut v_l_2077_: *mut LeanObject,
    mut v_r_2078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2079_: *mut LeanObject = core::ptr::null_mut();
    v_res_2079_ = l_Lean_KVMap_mergeBy(v_mergeFn_2076_, v_l_2077_, v_r_2078_);
    lean_dec(v_r_2078_);
    return v_res_2079_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(
    mut v_mergeFn_2080_: *mut LeanObject,
    mut v_as_2081_: *mut LeanObject,
    mut v_as_x27_2082_: *mut LeanObject,
    mut v_b_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    v___x_2085_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___redArg(
        v_mergeFn_2080_,
        v_as_x27_2082_,
        v_b_2083_,
    );
    return v___x_2085_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0___boxed(
    mut v_mergeFn_2086_: *mut LeanObject,
    mut v_as_2087_: *mut LeanObject,
    mut v_as_x27_2088_: *mut LeanObject,
    mut v_b_2089_: *mut LeanObject,
    mut v_a_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2091_: *mut LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_List_forIn_x27_loop___at___00Lean_KVMap_mergeBy_spec__0(
        v_mergeFn_2086_,
        v_as_2087_,
        v_as_x27_2088_,
        v_b_2089_,
        v_a_2090_,
    );
    lean_dec(v_as_x27_2088_);
    lean_dec(v_as_2087_);
    return v_res_2091_;
}
pub unsafe fn l_Lean_KVMap_eqv(
    mut v_m_u2081_2092_: *mut LeanObject,
    mut v_m_u2082_2093_: *mut LeanObject,
) -> u8 {
    let mut v___x_2094_: u8 = 0;
    lean_inc(v_m_u2081_2092_);
    v___x_2094_ = l_Lean_KVMap_subsetAux(v_m_u2081_2092_, v_m_u2082_2093_);
    if v___x_2094_ == 0 {
        lean_dec(v_m_u2082_2093_);
        lean_dec(v_m_u2081_2092_);
        return v___x_2094_;
    } else {
        let mut v___x_2095_: u8 = 0;
        v___x_2095_ = l_Lean_KVMap_subsetAux(v_m_u2082_2093_, v_m_u2081_2092_);
        lean_dec(v_m_u2081_2092_);
        return v___x_2095_;
    }
}
pub unsafe fn l_Lean_KVMap_eqv___boxed(
    mut v_m_u2081_2096_: *mut LeanObject,
    mut v_m_u2082_2097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2098_: u8 = 0;
    let mut v_r_2099_: *mut LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_KVMap_eqv(v_m_u2081_2096_, v_m_u2082_2097_);
    v_r_2099_ = lean_box((v_res_2098_) as usize);
    return v_r_2099_;
}
pub unsafe fn l_Lean_KVMap_get_x3f___redArg(
    mut v_inst_2102_: *mut LeanObject,
    mut v_m_2103_: *mut LeanObject,
    mut v_k_2104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofDataValue_x3f_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2105_ = lean_ctor_get(v_inst_2102_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2105_);
    lean_dec_ref(v_inst_2102_);
    v___x_2106_ = l_Lean_KVMap_findCore(v_m_2103_, v_k_2104_);
    if lean_obj_tag(v___x_2106_) == 0 {
        let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_2105_);
        v___x_2107_ = lean_box(0);
        return v___x_2107_;
    } else {
        let mut v_val_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
        v_val_2108_ = lean_ctor_get(v___x_2106_, 0);
        lean_inc(v_val_2108_);
        lean_dec_ref_known(v___x_2106_, 1);
        v___x_2109_ = lean_apply_1(v_ofDataValue_x3f_2105_, v_val_2108_);
        return v___x_2109_;
    }
}
pub unsafe fn l_Lean_KVMap_get_x3f___redArg___boxed(
    mut v_inst_2110_: *mut LeanObject,
    mut v_m_2111_: *mut LeanObject,
    mut v_k_2112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2113_: *mut LeanObject = core::ptr::null_mut();
    v_res_2113_ = l_Lean_KVMap_get_x3f___redArg(v_inst_2110_, v_m_2111_, v_k_2112_);
    lean_dec(v_k_2112_);
    lean_dec(v_m_2111_);
    return v_res_2113_;
}
pub unsafe fn l_Lean_KVMap_get_x3f(
    mut v_00_u03b1_2114_: *mut LeanObject,
    mut v_inst_2115_: *mut LeanObject,
    mut v_m_2116_: *mut LeanObject,
    mut v_k_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofDataValue_x3f_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2118_ = lean_ctor_get(v_inst_2115_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2118_);
    lean_dec_ref(v_inst_2115_);
    v___x_2119_ = l_Lean_KVMap_findCore(v_m_2116_, v_k_2117_);
    if lean_obj_tag(v___x_2119_) == 0 {
        let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_ofDataValue_x3f_2118_);
        v___x_2120_ = lean_box(0);
        return v___x_2120_;
    } else {
        let mut v_val_2121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
        v_val_2121_ = lean_ctor_get(v___x_2119_, 0);
        lean_inc(v_val_2121_);
        lean_dec_ref_known(v___x_2119_, 1);
        v___x_2122_ = lean_apply_1(v_ofDataValue_x3f_2118_, v_val_2121_);
        return v___x_2122_;
    }
}
pub unsafe fn l_Lean_KVMap_get_x3f___boxed(
    mut v_00_u03b1_2123_: *mut LeanObject,
    mut v_inst_2124_: *mut LeanObject,
    mut v_m_2125_: *mut LeanObject,
    mut v_k_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2127_: *mut LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lean_KVMap_get_x3f(v_00_u03b1_2123_, v_inst_2124_, v_m_2125_, v_k_2126_);
    lean_dec(v_k_2126_);
    lean_dec(v_m_2125_);
    return v_res_2127_;
}
pub unsafe fn l_Lean_KVMap_get___redArg(
    mut v_inst_2128_: *mut LeanObject,
    mut v_m_2129_: *mut LeanObject,
    mut v_k_2130_: *mut LeanObject,
    mut v_defVal_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofDataValue_x3f_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2132_ = lean_ctor_get(v_inst_2128_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2132_);
    lean_dec_ref(v_inst_2128_);
    v___x_2133_ = l_Lean_KVMap_findCore(v_m_2129_, v_k_2130_);
    if lean_obj_tag(v___x_2133_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_2132_);
        lean_inc(v_defVal_2131_);
        return v_defVal_2131_;
    } else {
        let mut v_val_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        v_val_2134_ = lean_ctor_get(v___x_2133_, 0);
        lean_inc(v_val_2134_);
        lean_dec_ref_known(v___x_2133_, 1);
        v___x_2135_ = lean_apply_1(v_ofDataValue_x3f_2132_, v_val_2134_);
        if lean_obj_tag(v___x_2135_) == 0 {
            lean_inc(v_defVal_2131_);
            return v_defVal_2131_;
        } else {
            let mut v_val_2136_: *mut LeanObject = core::ptr::null_mut();
            v_val_2136_ = lean_ctor_get(v___x_2135_, 0);
            lean_inc(v_val_2136_);
            lean_dec_ref_known(v___x_2135_, 1);
            return v_val_2136_;
        }
    }
}
pub unsafe fn l_Lean_KVMap_get___redArg___boxed(
    mut v_inst_2137_: *mut LeanObject,
    mut v_m_2138_: *mut LeanObject,
    mut v_k_2139_: *mut LeanObject,
    mut v_defVal_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2141_: *mut LeanObject = core::ptr::null_mut();
    v_res_2141_ = l_Lean_KVMap_get___redArg(v_inst_2137_, v_m_2138_, v_k_2139_, v_defVal_2140_);
    lean_dec(v_defVal_2140_);
    lean_dec(v_k_2139_);
    lean_dec(v_m_2138_);
    return v_res_2141_;
}
pub unsafe fn l_Lean_KVMap_get(
    mut v_00_u03b1_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_m_2144_: *mut LeanObject,
    mut v_k_2145_: *mut LeanObject,
    mut v_defVal_2146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ofDataValue_x3f_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    v_ofDataValue_x3f_2147_ = lean_ctor_get(v_inst_2143_, 1);
    lean_inc_ref(v_ofDataValue_x3f_2147_);
    lean_dec_ref(v_inst_2143_);
    v___x_2148_ = l_Lean_KVMap_findCore(v_m_2144_, v_k_2145_);
    if lean_obj_tag(v___x_2148_) == 0 {
        lean_dec_ref(v_ofDataValue_x3f_2147_);
        lean_inc(v_defVal_2146_);
        return v_defVal_2146_;
    } else {
        let mut v_val_2149_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
        v_val_2149_ = lean_ctor_get(v___x_2148_, 0);
        lean_inc(v_val_2149_);
        lean_dec_ref_known(v___x_2148_, 1);
        v___x_2150_ = lean_apply_1(v_ofDataValue_x3f_2147_, v_val_2149_);
        if lean_obj_tag(v___x_2150_) == 0 {
            lean_inc(v_defVal_2146_);
            return v_defVal_2146_;
        } else {
            let mut v_val_2151_: *mut LeanObject = core::ptr::null_mut();
            v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
            lean_inc(v_val_2151_);
            lean_dec_ref_known(v___x_2150_, 1);
            return v_val_2151_;
        }
    }
}
pub unsafe fn l_Lean_KVMap_get___boxed(
    mut v_00_u03b1_2152_: *mut LeanObject,
    mut v_inst_2153_: *mut LeanObject,
    mut v_m_2154_: *mut LeanObject,
    mut v_k_2155_: *mut LeanObject,
    mut v_defVal_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2157_: *mut LeanObject = core::ptr::null_mut();
    v_res_2157_ = l_Lean_KVMap_get(
        v_00_u03b1_2152_,
        v_inst_2153_,
        v_m_2154_,
        v_k_2155_,
        v_defVal_2156_,
    );
    lean_dec(v_defVal_2156_);
    lean_dec(v_k_2155_);
    lean_dec(v_m_2154_);
    return v_res_2157_;
}
pub unsafe fn l_Lean_KVMap_set___redArg(
    mut v_inst_2158_: *mut LeanObject,
    mut v_m_2159_: *mut LeanObject,
    mut v_k_2160_: *mut LeanObject,
    mut v_v_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    v_toDataValue_2162_ = lean_ctor_get(v_inst_2158_, 0);
    lean_inc_ref(v_toDataValue_2162_);
    lean_dec_ref(v_inst_2158_);
    v___x_2163_ = lean_apply_1(v_toDataValue_2162_, v_v_2161_);
    v___x_2164_ = l_Lean_KVMap_insertCore(v_m_2159_, v_k_2160_, v___x_2163_);
    return v___x_2164_;
}
pub unsafe fn l_Lean_KVMap_set(
    mut v_00_u03b1_2165_: *mut LeanObject,
    mut v_inst_2166_: *mut LeanObject,
    mut v_m_2167_: *mut LeanObject,
    mut v_k_2168_: *mut LeanObject,
    mut v_v_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    v_toDataValue_2170_ = lean_ctor_get(v_inst_2166_, 0);
    lean_inc_ref(v_toDataValue_2170_);
    lean_dec_ref(v_inst_2166_);
    v___x_2171_ = lean_apply_1(v_toDataValue_2170_, v_v_2169_);
    v___x_2172_ = l_Lean_KVMap_insertCore(v_m_2167_, v_k_2168_, v___x_2171_);
    return v___x_2172_;
}
pub unsafe fn l_Lean_KVMap_update___redArg(
    mut v_inst_2173_: *mut LeanObject,
    mut v_m_2174_: *mut LeanObject,
    mut v_k_2175_: *mut LeanObject,
    mut v_f_2176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2177_ = lean_ctor_get(v_inst_2173_, 0);
                lean_inc_ref(v_toDataValue_2177_);
                v_ofDataValue_x3f_2178_ = lean_ctor_get(v_inst_2173_, 1);
                lean_inc_ref(v_ofDataValue_x3f_2178_);
                lean_dec_ref(v_inst_2173_);
                v___x_2186_ = l_Lean_KVMap_findCore(v_m_2174_, v_k_2175_);
                if lean_obj_tag(v___x_2186_) == 0 {
                    lean_dec_ref(v_ofDataValue_x3f_2178_);
                    v___x_2187_ = lean_box(0);
                    v___y_2180_ = v___x_2187_;
                    state = 1;
                    continue;
                } else {
                    v_val_2188_ = lean_ctor_get(v___x_2186_, 0);
                    lean_inc(v_val_2188_);
                    lean_dec_ref_known(v___x_2186_, 1);
                    v___x_2189_ = lean_apply_1(v_ofDataValue_x3f_2178_, v_val_2188_);
                    v___y_2180_ = v___x_2189_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2181_ = lean_apply_1(v_f_2176_, v___y_2180_);
                if lean_obj_tag(v___x_2181_) == 0 {
                    lean_dec_ref(v_toDataValue_2177_);
                    v___x_2182_ = l_Lean_KVMap_erase(v_m_2174_, v_k_2175_);
                    lean_dec(v_k_2175_);
                    return v___x_2182_;
                } else {
                    v_val_2183_ = lean_ctor_get(v___x_2181_, 0);
                    lean_inc(v_val_2183_);
                    lean_dec_ref_known(v___x_2181_, 1);
                    v___x_2184_ = lean_apply_1(v_toDataValue_2177_, v_val_2183_);
                    v___x_2185_ = l_Lean_KVMap_insertCore(v_m_2174_, v_k_2175_, v___x_2184_);
                    return v___x_2185_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_update(
    mut v_00_u03b1_2190_: *mut LeanObject,
    mut v_inst_2191_: *mut LeanObject,
    mut v_m_2192_: *mut LeanObject,
    mut v_k_2193_: *mut LeanObject,
    mut v_f_2194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toDataValue_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofDataValue_x3f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toDataValue_2195_ = lean_ctor_get(v_inst_2191_, 0);
                lean_inc_ref(v_toDataValue_2195_);
                v_ofDataValue_x3f_2196_ = lean_ctor_get(v_inst_2191_, 1);
                lean_inc_ref(v_ofDataValue_x3f_2196_);
                lean_dec_ref(v_inst_2191_);
                v___x_2204_ = l_Lean_KVMap_findCore(v_m_2192_, v_k_2193_);
                if lean_obj_tag(v___x_2204_) == 0 {
                    lean_dec_ref(v_ofDataValue_x3f_2196_);
                    v___x_2205_ = lean_box(0);
                    v___y_2198_ = v___x_2205_;
                    state = 1;
                    continue;
                } else {
                    v_val_2206_ = lean_ctor_get(v___x_2204_, 0);
                    lean_inc(v_val_2206_);
                    lean_dec_ref_known(v___x_2204_, 1);
                    v___x_2207_ = lean_apply_1(v_ofDataValue_x3f_2196_, v_val_2206_);
                    v___y_2198_ = v___x_2207_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2199_ = lean_apply_1(v_f_2194_, v___y_2198_);
                if lean_obj_tag(v___x_2199_) == 0 {
                    lean_dec_ref(v_toDataValue_2195_);
                    v___x_2200_ = l_Lean_KVMap_erase(v_m_2192_, v_k_2193_);
                    lean_dec(v_k_2193_);
                    return v___x_2200_;
                } else {
                    v_val_2201_ = lean_ctor_get(v___x_2199_, 0);
                    lean_inc(v_val_2201_);
                    lean_dec_ref_known(v___x_2199_, 1);
                    v___x_2202_ = lean_apply_1(v_toDataValue_2195_, v_val_2201_);
                    v___x_2203_ = l_Lean_KVMap_insertCore(v_m_2192_, v_k_2193_, v___x_2202_);
                    return v___x_2203_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_KVMap_instValueDataValue___lam__0(
    mut v_val_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    v___x_2209_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2209_, 0, v_val_2208_);
    return v___x_2209_;
}
pub unsafe fn l_Lean_KVMap_instValueBool___lam__1(
    mut v_x_2216_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_2216_) == 1 {
        let mut v_v_2217_: u8 = 0;
        let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
        v_v_2217_ = lean_ctor_get_uint8(v_x_2216_, 0 as u32);
        v___x_2218_ = lean_box((v_v_2217_) as usize);
        v___x_2219_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2219_, 0, v___x_2218_);
        return v___x_2219_;
    } else {
        let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
        v___x_2220_ = lean_box(0);
        return v___x_2220_;
    }
}
pub unsafe fn l_Lean_KVMap_instValueBool___lam__1___boxed(
    mut v_x_2221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2222_: *mut LeanObject = core::ptr::null_mut();
    v_res_2222_ = l_Lean_KVMap_instValueBool___lam__1(v_x_2221_);
    lean_dec_ref(v_x_2221_);
    return v_res_2222_;
}
pub unsafe fn l_Lean_KVMap_instValueNat___lam__1(
    mut v_x_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2228_) == 3 {
                    v_v_2229_ = lean_ctor_get(v_x_2228_, 0);
                    v_isSharedCheck_2236_ = (!lean_is_exclusive(v_x_2228_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v_x_2228_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2229_);
                        lean_dec(v_x_2228_);
                        v___x_2231_ = lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2228_);
                    v___x_2237_ = lean_box(0);
                    return v___x_2237_;
                }
            }
            1 => {
                if v_isShared_2232_ == 0 {
                    lean_ctor_set_tag(v___x_2231_, 1);
                    v___x_2234_ = v___x_2231_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_v_2229_);
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
    mut v_x_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2247_: u8 = 0;
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2243_) == 4 {
                    v_v_2244_ = lean_ctor_get(v_x_2243_, 0);
                    v_isSharedCheck_2251_ = (!lean_is_exclusive(v_x_2243_)) as u8;
                    if v_isSharedCheck_2251_ == 0 {
                        v___x_2246_ = v_x_2243_;
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2244_);
                        lean_dec(v_x_2243_);
                        v___x_2246_ = lean_box(0);
                        v_isShared_2247_ = v_isSharedCheck_2251_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2243_);
                    v___x_2252_ = lean_box(0);
                    return v___x_2252_;
                }
            }
            1 => {
                if v_isShared_2247_ == 0 {
                    lean_ctor_set_tag(v___x_2246_, 1);
                    v___x_2249_ = v___x_2246_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_v_2244_);
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
    mut v_x_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2262_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2258_) == 2 {
                    v_v_2259_ = lean_ctor_get(v_x_2258_, 0);
                    v_isSharedCheck_2266_ = (!lean_is_exclusive(v_x_2258_)) as u8;
                    if v_isSharedCheck_2266_ == 0 {
                        v___x_2261_ = v_x_2258_;
                        v_isShared_2262_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2259_);
                        lean_dec(v_x_2258_);
                        v___x_2261_ = lean_box(0);
                        v_isShared_2262_ = v_isSharedCheck_2266_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2258_);
                    v___x_2267_ = lean_box(0);
                    return v___x_2267_;
                }
            }
            1 => {
                if v_isShared_2262_ == 0 {
                    lean_ctor_set_tag(v___x_2261_, 1);
                    v___x_2264_ = v___x_2261_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_v_2259_);
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
    mut v_x_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2277_: u8 = 0;
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2273_) == 0 {
                    v_v_2274_ = lean_ctor_get(v_x_2273_, 0);
                    v_isSharedCheck_2281_ = (!lean_is_exclusive(v_x_2273_)) as u8;
                    if v_isSharedCheck_2281_ == 0 {
                        v___x_2276_ = v_x_2273_;
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2274_);
                        lean_dec(v_x_2273_);
                        v___x_2276_ = lean_box(0);
                        v_isShared_2277_ = v_isSharedCheck_2281_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2273_);
                    v___x_2282_ = lean_box(0);
                    return v___x_2282_;
                }
            }
            1 => {
                if v_isShared_2277_ == 0 {
                    lean_ctor_set_tag(v___x_2276_, 1);
                    v___x_2279_ = v___x_2276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_v_2274_);
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
    mut v_x_2288_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2292_: u8 = 0;
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2296_: u8 = 0;
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2288_) == 5 {
                    v_v_2289_ = lean_ctor_get(v_x_2288_, 0);
                    v_isSharedCheck_2296_ = (!lean_is_exclusive(v_x_2288_)) as u8;
                    if v_isSharedCheck_2296_ == 0 {
                        v___x_2291_ = v_x_2288_;
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_v_2289_);
                        lean_dec(v_x_2288_);
                        v___x_2291_ = lean_box(0);
                        v_isShared_2292_ = v_isSharedCheck_2296_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_x_2288_);
                    v___x_2297_ = lean_box(0);
                    return v___x_2297_;
                }
            }
            1 => {
                if v_isShared_2292_ == 0 {
                    lean_ctor_set_tag(v___x_2291_, 1);
                    v___x_2294_ = v___x_2291_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_v_2289_);
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
pub unsafe fn runtime_initialize_Lean_Data_KVMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Format_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_instInhabitedKVMap_default = _init_l_Lean_instInhabitedKVMap_default();
    lean_mark_persistent(l_Lean_instInhabitedKVMap_default);
    l_Lean_instInhabitedKVMap = _init_l_Lean_instInhabitedKVMap();
    lean_mark_persistent(l_Lean_instInhabitedKVMap);
    l_Lean_KVMap_empty = _init_l_Lean_KVMap_empty();
    lean_mark_persistent(l_Lean_KVMap_empty);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_KVMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_KVMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Format_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Name(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Extra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_KVMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_KVMap(builtin);
}
