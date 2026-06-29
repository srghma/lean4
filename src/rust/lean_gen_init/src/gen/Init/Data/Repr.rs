// Lean compiler output
// Module: Init.Data.Repr
// Imports: Init.Data.Format.Basic Init.Control.Id Init.Data.UInt.BasicAux Init.Data.Char.Basic
use crate::r#gen::Init::Control::Id::{
    initialize_Init_Control_Id, runtime_initialize_Init_Control_Id,
};
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Format::Basic::{
    initialize_Init_Data_Format_Basic, l_Std_Format_defWidth, l_Std_Format_fill,
    l_Std_Format_joinSep___redArg, l_Std_Format_pretty, l_Std_instToFormatFormat___lam__0___boxed,
    runtime_initialize_Init_Data_Format_Basic,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_range, l_List_reverse___redArg};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::r#gen::Init::Prelude::l_System_Platform_numBits;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::Repr::lean_string_of_usize;
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_foldl, lean_string_isempty, lean_string_length,
    lean_string_push, lean_substring_tostring,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_nat, lean_uint16_to_nat, lean_uint64_to_nat, lean_usize_of_nat, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_pow, lean_nat_sub,
    lean_string_mk, lean_uint32_dec_eq, lean_uint32_to_nat,
};
pub static l_instReprEmpty___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprEmpty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprEmpty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprEmpty: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprEmpty___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Bool_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Bool_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Bool_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__2_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Bool_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Bool_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Bool_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_instReprBool___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Bool_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprBool___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprBool: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprBool___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Repr_addAppParen___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Repr_addAppParen___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Repr_addAppParen___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Repr_addAppParen___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Repr_addAppParen___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Repr_addAppParen___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Repr_addAppParen___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Repr_addAppParen___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Repr_addAppParen___closed__4_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Repr_addAppParen___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Repr_addAppParen___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Repr_addAppParen___closed__5_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Repr_addAppParen___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Repr_addAppParen___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [105, 115, 70, 97, 108, 115, 101, 32, 95, 0],
    };
static mut l_Decidable_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Decidable_repr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Decidable_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [105, 115, 84, 114, 117, 101, 32, 95, 0],
    };
static mut l_Decidable_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Decidable_repr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Decidable_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprDecidable___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Decidable_repr___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_instReprDecidable___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprDecidable___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprPUnit___lam__0___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [80, 85, 110, 105, 116, 46, 117, 110, 105, 116, 0],
    };
static mut l_instReprPUnit___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprPUnit___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprPUnit___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprPUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprPUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprPUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprPUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprULift___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [85, 76, 105, 102, 116, 46, 117, 112, 32, 0],
    };
static mut l_instReprULift___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprULift___redArg___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprULift___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprUnit___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [40, 41, 0],
    };
static mut l_instReprUnit___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUnit___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprUnit___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprUnit___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUnit___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUnit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUnit: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Option_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Option_repr___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Option_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___redArg___closed__2_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [115, 111, 109, 101, 32, 0],
    };
static mut l_Option_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Option_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Option_repr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Option_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [83, 117, 109, 46, 105, 110, 108, 32, 0],
    };
static mut l_Sum_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sum_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Sum_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__2_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [83, 117, 109, 46, 105, 110, 114, 32, 0],
    };
static mut l_Sum_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sum_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Sum_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Prod_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Prod_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Prod_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Prod_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__3_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Prod_repr___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Prod_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Prod_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Prod_repr___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Sigma_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Sigma_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [44, 32, 0],
    };
static mut l_Sigma_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__2_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Sigma_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Sigma_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Sigma_repr___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Sigma_repr___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Sigma_repr___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Sigma_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Repr_0__Nat_reprArray: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_reprFast___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_reprFast___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Nat_reprFast___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_reprFast___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instReprNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_hexDigitRepr___closed__0_value: crate::leanh::LeanStringObject<1> =
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
static mut l_hexDigitRepr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_hexDigitRepr___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 120, 0],
    };
static mut l_Char_quoteCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 39, 0],
    };
static mut l_Char_quoteCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 34, 0],
    };
static mut l_Char_quoteCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__3_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 92, 0],
    };
static mut l_Char_quoteCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__4_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 116, 0],
    };
static mut l_Char_quoteCore___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quoteCore___closed__5_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [92, 110, 0],
    };
static mut l_Char_quoteCore___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Char_quote___closed__0_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Char_quote___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quote___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprChar___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprChar___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprChar___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprChar: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprChar___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_quote___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_quote___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_String_quote___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_String_quote___closed__1_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [34, 0],
    };
static mut l_String_quote___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_String_quote___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [34, 34, 0],
    };
static mut l_String_quote___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instReprString___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprString: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__0_value: crate::leanh::LeanStringObject<14> =
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
        m_data: [123, 32, 98, 121, 116, 101, 73, 100, 120, 32, 58, 61, 32, 0],
    };
static mut l_instReprRaw___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprRaw___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprRaw___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__2_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_instReprRaw___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprRaw___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprRaw___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprRaw___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprRaw___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprRaw: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprRaw__1___lam__0___closed__0_value: crate::leanh::LeanStringObject<16> =
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
            46, 116, 111, 82, 97, 119, 83, 117, 98, 115, 116, 114, 105, 110, 103, 0,
        ],
    };
static mut l_instReprRaw__1___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprRaw__1___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprRaw__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprRaw__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprRaw__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprFin___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprFin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprFin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUInt8___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt8___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUInt8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt8___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUInt16___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt16___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUInt16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt16___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUInt32___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt32___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUInt32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt32___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUInt64___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt64___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUInt64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt64___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_instReprUSize___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUSize___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprUSize: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUSize___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___redArg___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_List_repr___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___redArg___closed__2_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_List_repr___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___redArg___closed__3_value: crate::leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_List_repr___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_repr___redArg___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_repr___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___redArg___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_repr___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___redArg___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_List_repr___redArg___closed__7_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__7_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprAtomBool: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomNat: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomInt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomChar: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomString: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt32: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt64: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUSize: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_instReprSourceInfo_repr___closed__0_value: crate::leanh::LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 46, 110, 111, 110,
            101, 0,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__2_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 46, 111, 114, 105,
            103, 105, 110, 97, 108, 0,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__3_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__2_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__4_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__3_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_instReprSourceInfo_repr___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprSourceInfo_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instReprSourceInfo_repr___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprSourceInfo_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprSourceInfo_repr___closed__7_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 46, 115, 121, 110,
            116, 104, 101, 116, 105, 99, 0,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__8_value: crate::leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__7_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__8_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_instReprSourceInfo___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprSourceInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprSourceInfo___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_instReprSourceInfo: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_repr___redArg(
    mut v_inst_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1102_ = crate::leanh::lean_apply_2(v_inst_1099_, v_a_1100_, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn l_repr(
    mut v_00_u03b1_1103_: *mut crate::leanh::LeanObject,
    mut v_inst_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1107_ = crate::leanh::lean_apply_2(v_inst_1104_, v_a_1105_, v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_reprStr___redArg(
    mut v_inst_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1111_ = crate::leanh::lean_apply_2(v_inst_1108_, v_a_1109_, v___x_1110_);
    v___x_1112_ = l_Std_Format_defWidth;
    v___x_1113_ = l_Std_Format_pretty(v___x_1111_, v___x_1112_, v___x_1110_, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn l_reprStr(
    mut v_00_u03b1_1114_: *mut crate::leanh::LeanObject,
    mut v_inst_1115_: *mut crate::leanh::LeanObject,
    mut v_a_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1118_ = crate::leanh::lean_apply_2(v_inst_1115_, v_a_1116_, v___x_1117_);
    v___x_1119_ = l_Std_Format_defWidth;
    v___x_1120_ = l_Std_Format_pretty(v___x_1118_, v___x_1119_, v___x_1117_, v___x_1117_);
    return v___x_1120_;
}
pub unsafe fn l_reprArg___redArg(
    mut v_inst_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1124_ = crate::leanh::lean_apply_2(v_inst_1121_, v_a_1122_, v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn l_reprArg(
    mut v_00_u03b1_1125_: *mut crate::leanh::LeanObject,
    mut v_inst_1126_: *mut crate::leanh::LeanObject,
    mut v_a_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1129_ = crate::leanh::lean_apply_2(v_inst_1126_, v_a_1127_, v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn l_instReprId___aux__1___redArg(
    mut v_inst_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1130_);
    return v_inst_1130_;
}
pub unsafe fn l_instReprId___aux__1___redArg___boxed(
    mut v_inst_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l_instReprId___aux__1___redArg(v_inst_1131_);
    crate::leanh::lean_dec_ref(v_inst_1131_);
    return v_res_1132_;
}
pub unsafe fn l_instReprId___aux__1(
    mut v_00_u03b1_1133_: *mut crate::leanh::LeanObject,
    mut v_inst_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1134_);
    return v_inst_1134_;
}
pub unsafe fn l_instReprId___aux__1___boxed(
    mut v_00_u03b1_1135_: *mut crate::leanh::LeanObject,
    mut v_inst_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_instReprId___aux__1(v_00_u03b1_1135_, v_inst_1136_);
    crate::leanh::lean_dec_ref(v_inst_1136_);
    return v_res_1137_;
}
pub unsafe fn l_instReprId___redArg(
    mut v_inst_1138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1138_);
    return v_inst_1138_;
}
pub unsafe fn l_instReprId___redArg___boxed(
    mut v_inst_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_instReprId___redArg(v_inst_1139_);
    crate::leanh::lean_dec_ref(v_inst_1139_);
    return v_res_1140_;
}
pub unsafe fn l_instReprId(
    mut v_00_u03b1_1141_: *mut crate::leanh::LeanObject,
    mut v_inst_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1142_);
    return v_inst_1142_;
}
pub unsafe fn l_instReprId___boxed(
    mut v_00_u03b1_1143_: *mut crate::leanh::LeanObject,
    mut v_inst_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_instReprId(v_00_u03b1_1143_, v_inst_1144_);
    crate::leanh::lean_dec_ref(v_inst_1144_);
    return v_res_1145_;
}
pub unsafe fn l_instReprId__1___aux__1___redArg(
    mut v_inst_1146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1146_);
    return v_inst_1146_;
}
pub unsafe fn l_instReprId__1___aux__1___redArg___boxed(
    mut v_inst_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_instReprId__1___aux__1___redArg(v_inst_1147_);
    crate::leanh::lean_dec_ref(v_inst_1147_);
    return v_res_1148_;
}
pub unsafe fn l_instReprId__1___aux__1(
    mut v_00_u03b1_1149_: *mut crate::leanh::LeanObject,
    mut v_inst_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1150_);
    return v_inst_1150_;
}
pub unsafe fn l_instReprId__1___aux__1___boxed(
    mut v_00_u03b1_1151_: *mut crate::leanh::LeanObject,
    mut v_inst_1152_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1153_ = l_instReprId__1___aux__1(v_00_u03b1_1151_, v_inst_1152_);
    crate::leanh::lean_dec_ref(v_inst_1152_);
    return v_res_1153_;
}
pub unsafe fn l_instReprId__1___redArg(
    mut v_inst_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1154_);
    return v_inst_1154_;
}
pub unsafe fn l_instReprId__1___redArg___boxed(
    mut v_inst_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_instReprId__1___redArg(v_inst_1155_);
    crate::leanh::lean_dec_ref(v_inst_1155_);
    return v_res_1156_;
}
pub unsafe fn l_instReprId__1(
    mut v_00_u03b1_1157_: *mut crate::leanh::LeanObject,
    mut v_inst_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_inst_1158_);
    return v_inst_1158_;
}
pub unsafe fn l_instReprId__1___boxed(
    mut v_00_u03b1_1159_: *mut crate::leanh::LeanObject,
    mut v_inst_1160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_instReprId__1(v_00_u03b1_1159_, v_inst_1160_);
    crate::leanh::lean_dec_ref(v_inst_1160_);
    return v_res_1161_;
}
pub unsafe fn l_instReprEmpty___lam__0(
    mut v_a_1162_: u8,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instReprEmpty___lam__0___boxed(
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_8__boxed_1166_: u8 = 0;
    let mut v_res_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_8__boxed_1166_ = (crate::leanh::lean_unbox(v_a_1164_) as u8);
    v_res_1167_ = l_instReprEmpty___lam__0(v_a_8__boxed_1166_, v_a_1165_);
    crate::leanh::lean_dec(v_a_1165_);
    return v_res_1167_;
}
pub unsafe fn l_Bool_repr___redArg(mut v_x_1176_: u8) -> *mut crate::leanh::LeanObject {
    if v_x_1176_ == 0 {
        let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1177_ = l_Bool_repr___redArg___closed__1;
        return v___x_1177_;
    } else {
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1178_ = l_Bool_repr___redArg___closed__3;
        return v___x_1178_;
    }
}
pub unsafe fn l_Bool_repr___redArg___boxed(
    mut v_x_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1180_ = (crate::leanh::lean_unbox(v_x_1179_) as u8);
    v_res_1181_ = l_Bool_repr___redArg(v_x_36__boxed_1180_);
    return v_res_1181_;
}
pub unsafe fn l_Bool_repr(
    mut v_x_1182_: u8,
    mut v_x_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1184_ = l_Bool_repr___redArg(v_x_1182_);
    return v___x_1184_;
}
pub unsafe fn l_Bool_repr___boxed(
    mut v_x_1185_: *mut crate::leanh::LeanObject,
    mut v_x_1186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_49__boxed_1187_: u8 = 0;
    let mut v_res_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_49__boxed_1187_ = (crate::leanh::lean_unbox(v_x_1185_) as u8);
    v_res_1188_ = l_Bool_repr(v_x_49__boxed_1187_, v_x_1186_);
    crate::leanh::lean_dec(v_x_1186_);
    return v_res_1188_;
}
pub unsafe fn l_Nat_cast___at___00Repr_addAppParen_spec__0(
    mut v_a_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = lean_nat_to_int(v_a_1191_);
    return v___x_1192_;
}
pub unsafe fn _init_l_Repr_addAppParen___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = l_Repr_addAppParen___closed__0;
    v___x_1196_ = lean_string_length(v___x_1195_);
    return v___x_1196_;
}
pub unsafe fn _init_l_Repr_addAppParen___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2),
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2_once),
        _init_l_Repr_addAppParen___closed__2,
    );
    v___x_1198_ = lean_nat_to_int(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Repr_addAppParen(
    mut v_f_1203_: *mut crate::leanh::LeanObject,
    mut v_prec_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    v___x_1205_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1206_ = lean_nat_dec_le(v___x_1205_, v_prec_1204_);
    if v___x_1206_ == 0 {
        return v_f_1203_;
    } else {
        let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1213_: u8 = 0;
        let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1207_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__3),
            core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__3_once),
            _init_l_Repr_addAppParen___closed__3,
        );
        v___x_1208_ = l_Repr_addAppParen___closed__4;
        v___x_1209_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
        crate::leanh::lean_ctor_set(v___x_1209_, 1, v_f_1203_);
        v___x_1210_ = l_Repr_addAppParen___closed__5;
        v___x_1211_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1211_, 0, v___x_1209_);
        crate::leanh::lean_ctor_set(v___x_1211_, 1, v___x_1210_);
        v___x_1212_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1212_, 0, v___x_1207_);
        crate::leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
        v___x_1213_ = 0;
        v___x_1214_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_1214_, 0, v___x_1212_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_1214_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_1213_,
        );
        return v___x_1214_;
    }
}
pub unsafe fn l_Repr_addAppParen___boxed(
    mut v_f_1215_: *mut crate::leanh::LeanObject,
    mut v_prec_1216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_Repr_addAppParen(v_f_1215_, v_prec_1216_);
    crate::leanh::lean_dec(v_prec_1216_);
    return v_res_1217_;
}
pub unsafe fn l_Decidable_repr___redArg(
    mut v_x_1224_: u8,
    mut v_x_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1224_ == 0 {
        let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1226_ = l_Decidable_repr___redArg___closed__1;
        v___x_1227_ = l_Repr_addAppParen(v___x_1226_, v_x_1225_);
        return v___x_1227_;
    } else {
        let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1228_ = l_Decidable_repr___redArg___closed__3;
        v___x_1229_ = l_Repr_addAppParen(v___x_1228_, v_x_1225_);
        return v___x_1229_;
    }
}
pub unsafe fn l_Decidable_repr___redArg___boxed(
    mut v_x_1230_: *mut crate::leanh::LeanObject,
    mut v_x_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_42__boxed_1232_: u8 = 0;
    let mut v_res_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1232_ = (crate::leanh::lean_unbox(v_x_1230_) as u8);
    v_res_1233_ = l_Decidable_repr___redArg(v_x_42__boxed_1232_, v_x_1231_);
    crate::leanh::lean_dec(v_x_1231_);
    return v_res_1233_;
}
pub unsafe fn l_Decidable_repr(
    mut v_p_1234_: *mut crate::leanh::LeanObject,
    mut v_x_1235_: u8,
    mut v_x_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Decidable_repr___redArg(v_x_1235_, v_x_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Decidable_repr___boxed(
    mut v_p_1238_: *mut crate::leanh::LeanObject,
    mut v_x_1239_: *mut crate::leanh::LeanObject,
    mut v_x_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_62__boxed_1241_: u8 = 0;
    let mut v_res_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_62__boxed_1241_ = (crate::leanh::lean_unbox(v_x_1239_) as u8);
    v_res_1242_ = l_Decidable_repr(v_p_1238_, v_x_62__boxed_1241_, v_x_1240_);
    crate::leanh::lean_dec(v_x_1240_);
    return v_res_1242_;
}
pub unsafe fn l_instReprDecidable(
    mut v_p_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = l_instReprDecidable___closed__0;
    return v___x_1245_;
}
pub unsafe fn l_instReprPUnit___lam__0(
    mut v_x_1249_: *mut crate::leanh::LeanObject,
    mut v_x_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_instReprPUnit___lam__0___closed__1;
    return v___x_1251_;
}
pub unsafe fn l_instReprPUnit___lam__0___boxed(
    mut v_x_1252_: *mut crate::leanh::LeanObject,
    mut v_x_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_instReprPUnit___lam__0(v_x_1252_, v_x_1253_);
    crate::leanh::lean_dec(v_x_1253_);
    return v_res_1254_;
}
pub unsafe fn l_instReprULift___redArg___lam__0(
    mut v_inst_1260_: *mut crate::leanh::LeanObject,
    mut v_v_1261_: *mut crate::leanh::LeanObject,
    mut v_prec_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = l_instReprULift___redArg___lam__0___closed__1;
    v___x_1264_ = crate::leanh::lean_unsigned_to_nat(1024);
    v___x_1265_ = crate::leanh::lean_apply_2(v_inst_1260_, v_v_1261_, v___x_1264_);
    v___x_1266_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1266_, 0, v___x_1263_);
    crate::leanh::lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    v___x_1267_ = l_Repr_addAppParen(v___x_1266_, v_prec_1262_);
    return v___x_1267_;
}
pub unsafe fn l_instReprULift___redArg___lam__0___boxed(
    mut v_inst_1268_: *mut crate::leanh::LeanObject,
    mut v_v_1269_: *mut crate::leanh::LeanObject,
    mut v_prec_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_instReprULift___redArg___lam__0(v_inst_1268_, v_v_1269_, v_prec_1270_);
    crate::leanh::lean_dec(v_prec_1270_);
    return v_res_1271_;
}
pub unsafe fn l_instReprULift___redArg(
    mut v_inst_1272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1273_ = crate::leanh::lean_alloc_closure(
        l_instReprULift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1273_, 0, v_inst_1272_);
    return v___f_1273_;
}
pub unsafe fn l_instReprULift(
    mut v_00_u03b1_1274_: *mut crate::leanh::LeanObject,
    mut v_inst_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1276_ = crate::leanh::lean_alloc_closure(
        l_instReprULift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1276_, 0, v_inst_1275_);
    return v___f_1276_;
}
pub unsafe fn l_instReprUnit___lam__0(
    mut v_x_1280_: *mut crate::leanh::LeanObject,
    mut v_x_1281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_instReprUnit___lam__0___closed__1;
    return v___x_1282_;
}
pub unsafe fn l_instReprUnit___lam__0___boxed(
    mut v_x_1283_: *mut crate::leanh::LeanObject,
    mut v_x_1284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_instReprUnit___lam__0(v_x_1283_, v_x_1284_);
    crate::leanh::lean_dec(v_x_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Option_repr___redArg(
    mut v_inst_1294_: *mut crate::leanh::LeanObject,
    mut v_x_1295_: *mut crate::leanh::LeanObject,
    mut v_x_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1295_) == 0 {
        let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1294_);
        v___x_1297_ = l_Option_repr___redArg___closed__1;
        return v___x_1297_;
    } else {
        let mut v_val_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1298_ = crate::leanh::lean_ctor_get(v_x_1295_, 0);
        crate::leanh::lean_inc(v_val_1298_);
        crate::leanh::lean_dec_ref_known(v_x_1295_, 1);
        v___x_1299_ = l_Option_repr___redArg___closed__3;
        v___x_1300_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_1301_ = crate::leanh::lean_apply_2(v_inst_1294_, v_val_1298_, v___x_1300_);
        v___x_1302_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1299_);
        crate::leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
        v___x_1303_ = l_Repr_addAppParen(v___x_1302_, v_x_1296_);
        return v___x_1303_;
    }
}
pub unsafe fn l_Option_repr___redArg___boxed(
    mut v_inst_1304_: *mut crate::leanh::LeanObject,
    mut v_x_1305_: *mut crate::leanh::LeanObject,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Option_repr___redArg(v_inst_1304_, v_x_1305_, v_x_1306_);
    crate::leanh::lean_dec(v_x_1306_);
    return v_res_1307_;
}
pub unsafe fn l_Option_repr(
    mut v_00_u03b1_1308_: *mut crate::leanh::LeanObject,
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Option_repr___redArg(v_inst_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Option_repr___boxed(
    mut v_00_u03b1_1313_: *mut crate::leanh::LeanObject,
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_x_1315_: *mut crate::leanh::LeanObject,
    mut v_x_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Option_repr(v_00_u03b1_1313_, v_inst_1314_, v_x_1315_, v_x_1316_);
    crate::leanh::lean_dec(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_instReprOption___redArg(
    mut v_inst_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        crate::leanh::lean_alloc_closure(l_Option_repr___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1319_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1319_, 1, v_inst_1318_);
    return v___x_1319_;
}
pub unsafe fn l_instReprOption(
    mut v_00_u03b1_1320_: *mut crate::leanh::LeanObject,
    mut v_inst_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ =
        crate::leanh::lean_alloc_closure(l_Option_repr___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_1322_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1322_, 1, v_inst_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Sum_repr___redArg(
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
    mut v_x_1331_: *mut crate::leanh::LeanObject,
    mut v_x_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1331_) == 0 {
        let mut v_val_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1330_);
        v_val_1333_ = crate::leanh::lean_ctor_get(v_x_1331_, 0);
        crate::leanh::lean_inc(v_val_1333_);
        crate::leanh::lean_dec_ref_known(v_x_1331_, 1);
        v___x_1334_ = l_Sum_repr___redArg___closed__1;
        v___x_1335_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_1336_ = crate::leanh::lean_apply_2(v_inst_1329_, v_val_1333_, v___x_1335_);
        v___x_1337_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1337_, 0, v___x_1334_);
        crate::leanh::lean_ctor_set(v___x_1337_, 1, v___x_1336_);
        v___x_1338_ = l_Repr_addAppParen(v___x_1337_, v_x_1332_);
        return v___x_1338_;
    } else {
        let mut v_val_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_1329_);
        v_val_1339_ = crate::leanh::lean_ctor_get(v_x_1331_, 0);
        crate::leanh::lean_inc(v_val_1339_);
        crate::leanh::lean_dec_ref_known(v_x_1331_, 1);
        v___x_1340_ = l_Sum_repr___redArg___closed__3;
        v___x_1341_ = crate::leanh::lean_unsigned_to_nat(1024);
        v___x_1342_ = crate::leanh::lean_apply_2(v_inst_1330_, v_val_1339_, v___x_1341_);
        v___x_1343_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1343_, 0, v___x_1340_);
        crate::leanh::lean_ctor_set(v___x_1343_, 1, v___x_1342_);
        v___x_1344_ = l_Repr_addAppParen(v___x_1343_, v_x_1332_);
        return v___x_1344_;
    }
}
pub unsafe fn l_Sum_repr___redArg___boxed(
    mut v_inst_1345_: *mut crate::leanh::LeanObject,
    mut v_inst_1346_: *mut crate::leanh::LeanObject,
    mut v_x_1347_: *mut crate::leanh::LeanObject,
    mut v_x_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Sum_repr___redArg(v_inst_1345_, v_inst_1346_, v_x_1347_, v_x_1348_);
    crate::leanh::lean_dec(v_x_1348_);
    return v_res_1349_;
}
pub unsafe fn l_Sum_repr(
    mut v_00_u03b1_1350_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1351_: *mut crate::leanh::LeanObject,
    mut v_inst_1352_: *mut crate::leanh::LeanObject,
    mut v_inst_1353_: *mut crate::leanh::LeanObject,
    mut v_x_1354_: *mut crate::leanh::LeanObject,
    mut v_x_1355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Sum_repr___redArg(v_inst_1352_, v_inst_1353_, v_x_1354_, v_x_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Sum_repr___boxed(
    mut v_00_u03b1_1357_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut crate::leanh::LeanObject,
    mut v_inst_1359_: *mut crate::leanh::LeanObject,
    mut v_inst_1360_: *mut crate::leanh::LeanObject,
    mut v_x_1361_: *mut crate::leanh::LeanObject,
    mut v_x_1362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Sum_repr(
        v_00_u03b1_1357_,
        v_00_u03b2_1358_,
        v_inst_1359_,
        v_inst_1360_,
        v_x_1361_,
        v_x_1362_,
    );
    crate::leanh::lean_dec(v_x_1362_);
    return v_res_1363_;
}
pub unsafe fn l_instReprSum___redArg(
    mut v_inst_1364_: *mut crate::leanh::LeanObject,
    mut v_inst_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ =
        crate::leanh::lean_alloc_closure(l_Sum_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1366_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1366_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1366_, 2, v_inst_1364_);
    crate::leanh::lean_closure_set(v___x_1366_, 3, v_inst_1365_);
    return v___x_1366_;
}
pub unsafe fn l_instReprSum(
    mut v_00_u03b1_1367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1368_: *mut crate::leanh::LeanObject,
    mut v_inst_1369_: *mut crate::leanh::LeanObject,
    mut v_inst_1370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ =
        crate::leanh::lean_alloc_closure(l_Sum_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1371_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1371_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1371_, 2, v_inst_1369_);
    crate::leanh::lean_closure_set(v___x_1371_, 3, v_inst_1370_);
    return v___x_1371_;
}
pub unsafe fn l_instReprTupleOfRepr___redArg___lam__0(
    mut v_inst_1372_: *mut crate::leanh::LeanObject,
    mut v_a_1373_: *mut crate::leanh::LeanObject,
    mut v_xs_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1376_ = crate::leanh::lean_apply_2(v_inst_1372_, v_a_1373_, v___x_1375_);
    v___x_1377_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
    crate::leanh::lean_ctor_set(v___x_1377_, 1, v_xs_1374_);
    return v___x_1377_;
}
pub unsafe fn l_instReprTupleOfRepr___redArg(
    mut v_inst_1378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1379_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1379_, 0, v_inst_1378_);
    return v___f_1379_;
}
pub unsafe fn l_instReprTupleOfRepr(
    mut v_00_u03b1_1380_: *mut crate::leanh::LeanObject,
    mut v_inst_1381_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1382_ = crate::leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1382_, 0, v_inst_1381_);
    return v___f_1382_;
}
pub unsafe fn l_Prod_reprTuple___redArg(
    mut v_inst_1383_: *mut crate::leanh::LeanObject,
    mut v_inst_1384_: *mut crate::leanh::LeanObject,
    mut v_x_1385_: *mut crate::leanh::LeanObject,
    mut v_x_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1387_ = crate::leanh::lean_ctor_get(v_x_1385_, 0);
                v_snd_1388_ = crate::leanh::lean_ctor_get(v_x_1385_, 1);
                v_isSharedCheck_1398_ = (!crate::leanh::lean_is_exclusive(v_x_1385_)) as u8;
                if v_isSharedCheck_1398_ == 0 {
                    v___x_1390_ = v_x_1385_;
                    v_isShared_1391_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1388_);
                    crate::leanh::lean_inc(v_fst_1387_);
                    crate::leanh::lean_dec(v_x_1385_);
                    v___x_1390_ = crate::leanh::lean_box(0);
                    v_isShared_1391_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1392_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1393_ = crate::leanh::lean_apply_2(v_inst_1383_, v_fst_1387_, v___x_1392_);
                if v_isShared_1391_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1390_, 1);
                    crate::leanh::lean_ctor_set(v___x_1390_, 1, v_x_1386_);
                    crate::leanh::lean_ctor_set(v___x_1390_, 0, v___x_1393_);
                    v___x_1395_ = v___x_1390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_x_1386_);
                    v___x_1395_ = v_reuseFailAlloc_1397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1396_ = crate::leanh::lean_apply_2(v_inst_1384_, v_snd_1388_, v___x_1395_);
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_reprTuple(
    mut v_00_u03b1_1399_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1400_: *mut crate::leanh::LeanObject,
    mut v_inst_1401_: *mut crate::leanh::LeanObject,
    mut v_inst_1402_: *mut crate::leanh::LeanObject,
    mut v_x_1403_: *mut crate::leanh::LeanObject,
    mut v_x_1404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Prod_reprTuple___redArg(v_inst_1401_, v_inst_1402_, v_x_1403_, v_x_1404_);
    return v___x_1405_;
}
pub unsafe fn l_instReprTupleProdOfRepr___redArg(
    mut v_inst_1406_: *mut crate::leanh::LeanObject,
    mut v_inst_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ =
        crate::leanh::lean_alloc_closure(l_Prod_reprTuple as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1408_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1408_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1408_, 2, v_inst_1406_);
    crate::leanh::lean_closure_set(v___x_1408_, 3, v_inst_1407_);
    return v___x_1408_;
}
pub unsafe fn l_instReprTupleProdOfRepr(
    mut v_00_u03b1_1409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1410_: *mut crate::leanh::LeanObject,
    mut v_inst_1411_: *mut crate::leanh::LeanObject,
    mut v_inst_1412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ =
        crate::leanh::lean_alloc_closure(l_Prod_reprTuple as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1413_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1413_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1413_, 2, v_inst_1411_);
    crate::leanh::lean_closure_set(v___x_1413_, 3, v_inst_1412_);
    return v___x_1413_;
}
pub unsafe fn _init_l_Prod_repr___redArg___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2),
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2_once),
        _init_l_Repr_addAppParen___closed__2,
    );
    v___x_1422_ = lean_nat_to_int(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Prod_repr___redArg(
    mut v_inst_1423_: *mut crate::leanh::LeanObject,
    mut v_inst_1424_: *mut crate::leanh::LeanObject,
    mut v_x_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___f_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1426_ = crate::leanh::lean_ctor_get(v_x_1425_, 0);
                v_snd_1427_ = crate::leanh::lean_ctor_get(v_x_1425_, 1);
                v_isSharedCheck_1450_ = (!crate::leanh::lean_is_exclusive(v_x_1425_)) as u8;
                if v_isSharedCheck_1450_ == 0 {
                    v___x_1429_ = v_x_1425_;
                    v_isShared_1430_ = v_isSharedCheck_1450_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1427_);
                    crate::leanh::lean_inc(v_fst_1426_);
                    crate::leanh::lean_dec(v_x_1425_);
                    v___x_1429_ = crate::leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1450_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1431_ = l_Prod_repr___redArg___closed__0;
                v___x_1432_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1433_ = crate::leanh::lean_apply_2(v_inst_1423_, v_fst_1426_, v___x_1432_);
                v___x_1434_ = crate::leanh::lean_box(0);
                if v_isShared_1430_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1429_, 1);
                    crate::leanh::lean_ctor_set(v___x_1429_, 1, v___x_1434_);
                    crate::leanh::lean_ctor_set(v___x_1429_, 0, v___x_1433_);
                    v___x_1436_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1449_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1434_);
                    v___x_1436_ = v_reuseFailAlloc_1449_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1437_ = crate::leanh::lean_apply_2(v_inst_1424_, v_snd_1427_, v___x_1436_);
                v___x_1438_ = l_List_reverse___redArg(v___x_1437_);
                v___x_1439_ = l_Prod_repr___redArg___closed__3;
                v___x_1440_ = l_Std_Format_joinSep___redArg(v___f_1431_, v___x_1438_, v___x_1439_);
                v___x_1441_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Prod_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Prod_repr___redArg___closed__4_once),
                    _init_l_Prod_repr___redArg___closed__4,
                );
                v___x_1442_ = l_Repr_addAppParen___closed__4;
                v___x_1443_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
                crate::leanh::lean_ctor_set(v___x_1443_, 1, v___x_1440_);
                v___x_1444_ = l_Repr_addAppParen___closed__5;
                v___x_1445_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1445_, 0, v___x_1443_);
                crate::leanh::lean_ctor_set(v___x_1445_, 1, v___x_1444_);
                v___x_1446_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1446_, 0, v___x_1441_);
                crate::leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = 0;
                v___x_1448_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1446_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1448_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1447_,
                );
                return v___x_1448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_repr(
    mut v_00_u03b1_1451_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1452_: *mut crate::leanh::LeanObject,
    mut v_inst_1453_: *mut crate::leanh::LeanObject,
    mut v_inst_1454_: *mut crate::leanh::LeanObject,
    mut v_x_1455_: *mut crate::leanh::LeanObject,
    mut v_x_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Prod_repr___redArg(v_inst_1453_, v_inst_1454_, v_x_1455_);
    return v___x_1457_;
}
pub unsafe fn l_Prod_repr___boxed(
    mut v_00_u03b1_1458_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1459_: *mut crate::leanh::LeanObject,
    mut v_inst_1460_: *mut crate::leanh::LeanObject,
    mut v_inst_1461_: *mut crate::leanh::LeanObject,
    mut v_x_1462_: *mut crate::leanh::LeanObject,
    mut v_x_1463_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Prod_repr(
        v_00_u03b1_1458_,
        v_00_u03b2_1459_,
        v_inst_1460_,
        v_inst_1461_,
        v_x_1462_,
        v_x_1463_,
    );
    crate::leanh::lean_dec(v_x_1463_);
    return v_res_1464_;
}
pub unsafe fn l_instReprProdOfReprTuple___redArg(
    mut v_inst_1465_: *mut crate::leanh::LeanObject,
    mut v_inst_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1467_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1467_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1467_, 2, v_inst_1465_);
    crate::leanh::lean_closure_set(v___x_1467_, 3, v_inst_1466_);
    return v___x_1467_;
}
pub unsafe fn l_instReprProdOfReprTuple(
    mut v_00_u03b1_1468_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1469_: *mut crate::leanh::LeanObject,
    mut v_inst_1470_: *mut crate::leanh::LeanObject,
    mut v_inst_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ =
        crate::leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1472_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1472_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1472_, 2, v_inst_1470_);
    crate::leanh::lean_closure_set(v___x_1472_, 3, v_inst_1471_);
    return v___x_1472_;
}
pub unsafe fn _init_l_Sigma_repr___redArg___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Sigma_repr___redArg___closed__0;
    v___x_1479_ = lean_string_length(v___x_1478_);
    return v___x_1479_;
}
pub unsafe fn _init_l_Sigma_repr___redArg___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__4_once),
        _init_l_Sigma_repr___redArg___closed__4,
    );
    v___x_1481_ = lean_nat_to_int(v___x_1480_);
    return v___x_1481_;
}
pub unsafe fn l_Sigma_repr___redArg(
    mut v_inst_1486_: *mut crate::leanh::LeanObject,
    mut v_inst_1487_: *mut crate::leanh::LeanObject,
    mut v_x_1488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1489_ = crate::leanh::lean_ctor_get(v_x_1488_, 0);
                v_snd_1490_ = crate::leanh::lean_ctor_get(v_x_1488_, 1);
                v_isSharedCheck_1510_ = (!crate::leanh::lean_is_exclusive(v_x_1488_)) as u8;
                if v_isSharedCheck_1510_ == 0 {
                    v___x_1492_ = v_x_1488_;
                    v_isShared_1493_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1490_);
                    crate::leanh::lean_inc(v_fst_1489_);
                    crate::leanh::lean_dec(v_x_1488_);
                    v___x_1492_ = crate::leanh::lean_box(0);
                    v_isShared_1493_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1494_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc(v_fst_1489_);
                v___x_1495_ = crate::leanh::lean_apply_2(v_inst_1486_, v_fst_1489_, v___x_1494_);
                v___x_1496_ = l_Sigma_repr___redArg___closed__2;
                if v_isShared_1493_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1492_, 5);
                    crate::leanh::lean_ctor_set(v___x_1492_, 1, v___x_1496_);
                    crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1495_);
                    v___x_1498_ = v___x_1492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1496_);
                    v___x_1498_ = v_reuseFailAlloc_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1499_ =
                    crate::leanh::lean_apply_3(v_inst_1487_, v_fst_1489_, v_snd_1490_, v___x_1494_);
                v___x_1500_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1500_, 0, v___x_1498_);
                crate::leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
                v___x_1501_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__5_once),
                    _init_l_Sigma_repr___redArg___closed__5,
                );
                v___x_1502_ = l_Sigma_repr___redArg___closed__6;
                v___x_1503_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1503_, 0, v___x_1502_);
                crate::leanh::lean_ctor_set(v___x_1503_, 1, v___x_1500_);
                v___x_1504_ = l_Sigma_repr___redArg___closed__7;
                v___x_1505_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                crate::leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                v___x_1506_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1506_, 0, v___x_1501_);
                crate::leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
                v___x_1507_ = 0;
                v___x_1508_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_1508_, 0, v___x_1506_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1508_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1507_,
                );
                return v___x_1508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Sigma_repr(
    mut v_00_u03b1_1511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1512_: *mut crate::leanh::LeanObject,
    mut v_inst_1513_: *mut crate::leanh::LeanObject,
    mut v_inst_1514_: *mut crate::leanh::LeanObject,
    mut v_x_1515_: *mut crate::leanh::LeanObject,
    mut v_x_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_Sigma_repr___redArg(v_inst_1513_, v_inst_1514_, v_x_1515_);
    return v___x_1517_;
}
pub unsafe fn l_Sigma_repr___boxed(
    mut v_00_u03b1_1518_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1519_: *mut crate::leanh::LeanObject,
    mut v_inst_1520_: *mut crate::leanh::LeanObject,
    mut v_inst_1521_: *mut crate::leanh::LeanObject,
    mut v_x_1522_: *mut crate::leanh::LeanObject,
    mut v_x_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Sigma_repr(
        v_00_u03b1_1518_,
        v_00_u03b2_1519_,
        v_inst_1520_,
        v_inst_1521_,
        v_x_1522_,
        v_x_1523_,
    );
    crate::leanh::lean_dec(v_x_1523_);
    return v_res_1524_;
}
pub unsafe fn l_instReprSigma___redArg(
    mut v_inst_1525_: *mut crate::leanh::LeanObject,
    mut v_inst_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ =
        crate::leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1527_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1527_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1527_, 2, v_inst_1525_);
    crate::leanh::lean_closure_set(v___x_1527_, 3, v_inst_1526_);
    return v___x_1527_;
}
pub unsafe fn l_instReprSigma(
    mut v_00_u03b1_1528_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1529_: *mut crate::leanh::LeanObject,
    mut v_inst_1530_: *mut crate::leanh::LeanObject,
    mut v_inst_1531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ =
        crate::leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    crate::leanh::lean_closure_set(v___x_1532_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1532_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1532_, 2, v_inst_1530_);
    crate::leanh::lean_closure_set(v___x_1532_, 3, v_inst_1531_);
    return v___x_1532_;
}
pub unsafe fn l_instReprSubtype___redArg___lam__0(
    mut v_inst_1533_: *mut crate::leanh::LeanObject,
    mut v_s_1534_: *mut crate::leanh::LeanObject,
    mut v_prec_1535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = crate::leanh::lean_apply_2(v_inst_1533_, v_s_1534_, v_prec_1535_);
    return v___x_1536_;
}
pub unsafe fn l_instReprSubtype___redArg(
    mut v_inst_1537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1538_ = crate::leanh::lean_alloc_closure(
        l_instReprSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1538_, 0, v_inst_1537_);
    return v___f_1538_;
}
pub unsafe fn l_instReprSubtype(
    mut v_00_u03b1_1539_: *mut crate::leanh::LeanObject,
    mut v_p_1540_: *mut crate::leanh::LeanObject,
    mut v_inst_1541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1542_ = crate::leanh::lean_alloc_closure(
        l_instReprSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1542_, 0, v_inst_1541_);
    return v___f_1542_;
}
pub unsafe fn l_Nat_digitChar(mut v_n_1543_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    v___x_1544_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1545_ = lean_nat_dec_eq(v_n_1543_, v___x_1544_);
    if v___x_1545_ == 0 {
        let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: u8 = 0;
        v___x_1546_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1547_ = lean_nat_dec_eq(v_n_1543_, v___x_1546_);
        if v___x_1547_ == 0 {
            let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1549_: u8 = 0;
            v___x_1548_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_1549_ = lean_nat_dec_eq(v_n_1543_, v___x_1548_);
            if v___x_1549_ == 0 {
                let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1551_: u8 = 0;
                v___x_1550_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1551_ = lean_nat_dec_eq(v_n_1543_, v___x_1550_);
                if v___x_1551_ == 0 {
                    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1553_: u8 = 0;
                    v___x_1552_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1553_ = lean_nat_dec_eq(v_n_1543_, v___x_1552_);
                    if v___x_1553_ == 0 {
                        let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1555_: u8 = 0;
                        v___x_1554_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_1555_ = lean_nat_dec_eq(v_n_1543_, v___x_1554_);
                        if v___x_1555_ == 0 {
                            let mut v___x_1556_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1557_: u8 = 0;
                            v___x_1556_ = crate::leanh::lean_unsigned_to_nat(6);
                            v___x_1557_ = lean_nat_dec_eq(v_n_1543_, v___x_1556_);
                            if v___x_1557_ == 0 {
                                let mut v___x_1558_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1559_: u8 = 0;
                                v___x_1558_ = crate::leanh::lean_unsigned_to_nat(7);
                                v___x_1559_ = lean_nat_dec_eq(v_n_1543_, v___x_1558_);
                                if v___x_1559_ == 0 {
                                    let mut v___x_1560_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1561_: u8 = 0;
                                    v___x_1560_ = crate::leanh::lean_unsigned_to_nat(8);
                                    v___x_1561_ = lean_nat_dec_eq(v_n_1543_, v___x_1560_);
                                    if v___x_1561_ == 0 {
                                        let mut v___x_1562_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1563_: u8 = 0;
                                        v___x_1562_ = crate::leanh::lean_unsigned_to_nat(9);
                                        v___x_1563_ = lean_nat_dec_eq(v_n_1543_, v___x_1562_);
                                        if v___x_1563_ == 0 {
                                            let mut v___x_1564_: *mut crate::leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_1565_: u8 = 0;
                                            v___x_1564_ = crate::leanh::lean_unsigned_to_nat(10);
                                            v___x_1565_ = lean_nat_dec_eq(v_n_1543_, v___x_1564_);
                                            if v___x_1565_ == 0 {
                                                let mut v___x_1566_: *mut crate::leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_1567_: u8 = 0;
                                                v___x_1566_ =
                                                    crate::leanh::lean_unsigned_to_nat(11);
                                                v___x_1567_ =
                                                    lean_nat_dec_eq(v_n_1543_, v___x_1566_);
                                                if v___x_1567_ == 0 {
                                                    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_1569_: u8 = 0;
                                                    v___x_1568_ =
                                                        crate::leanh::lean_unsigned_to_nat(12);
                                                    v___x_1569_ =
                                                        lean_nat_dec_eq(v_n_1543_, v___x_1568_);
                                                    if v___x_1569_ == 0 {
                                                        let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_1571_: u8 = 0;
                                                        v___x_1570_ =
                                                            crate::leanh::lean_unsigned_to_nat(13);
                                                        v___x_1571_ =
                                                            lean_nat_dec_eq(v_n_1543_, v___x_1570_);
                                                        if v___x_1571_ == 0 {
                                                            let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_1573_: u8 = 0;
                                                            v___x_1572_ =
                                                                crate::leanh::lean_unsigned_to_nat(
                                                                    14,
                                                                );
                                                            v___x_1573_ = lean_nat_dec_eq(
                                                                v_n_1543_,
                                                                v___x_1572_,
                                                            );
                                                            if v___x_1573_ == 0 {
                                                                let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_1575_: u8 = 0;
                                                                v___x_1574_ = crate::leanh::lean_unsigned_to_nat(15);
                                                                v___x_1575_ = lean_nat_dec_eq(
                                                                    v_n_1543_,
                                                                    v___x_1574_,
                                                                );
                                                                if v___x_1575_ == 0 {
                                                                    let mut v___x_1576_: u32 = 0;
                                                                    v___x_1576_ = 42;
                                                                    return v___x_1576_;
                                                                } else {
                                                                    let mut v___x_1577_: u32 = 0;
                                                                    v___x_1577_ = 102;
                                                                    return v___x_1577_;
                                                                }
                                                            } else {
                                                                let mut v___x_1578_: u32 = 0;
                                                                v___x_1578_ = 101;
                                                                return v___x_1578_;
                                                            }
                                                        } else {
                                                            let mut v___x_1579_: u32 = 0;
                                                            v___x_1579_ = 100;
                                                            return v___x_1579_;
                                                        }
                                                    } else {
                                                        let mut v___x_1580_: u32 = 0;
                                                        v___x_1580_ = 99;
                                                        return v___x_1580_;
                                                    }
                                                } else {
                                                    let mut v___x_1581_: u32 = 0;
                                                    v___x_1581_ = 98;
                                                    return v___x_1581_;
                                                }
                                            } else {
                                                let mut v___x_1582_: u32 = 0;
                                                v___x_1582_ = 97;
                                                return v___x_1582_;
                                            }
                                        } else {
                                            let mut v___x_1583_: u32 = 0;
                                            v___x_1583_ = 57;
                                            return v___x_1583_;
                                        }
                                    } else {
                                        let mut v___x_1584_: u32 = 0;
                                        v___x_1584_ = 56;
                                        return v___x_1584_;
                                    }
                                } else {
                                    let mut v___x_1585_: u32 = 0;
                                    v___x_1585_ = 55;
                                    return v___x_1585_;
                                }
                            } else {
                                let mut v___x_1586_: u32 = 0;
                                v___x_1586_ = 54;
                                return v___x_1586_;
                            }
                        } else {
                            let mut v___x_1587_: u32 = 0;
                            v___x_1587_ = 53;
                            return v___x_1587_;
                        }
                    } else {
                        let mut v___x_1588_: u32 = 0;
                        v___x_1588_ = 52;
                        return v___x_1588_;
                    }
                } else {
                    let mut v___x_1589_: u32 = 0;
                    v___x_1589_ = 51;
                    return v___x_1589_;
                }
            } else {
                let mut v___x_1590_: u32 = 0;
                v___x_1590_ = 50;
                return v___x_1590_;
            }
        } else {
            let mut v___x_1591_: u32 = 0;
            v___x_1591_ = 49;
            return v___x_1591_;
        }
    } else {
        let mut v___x_1592_: u32 = 0;
        v___x_1592_ = 48;
        return v___x_1592_;
    }
}
pub unsafe fn l_Nat_digitChar___boxed(
    mut v_n_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1594_: u32 = 0;
    let mut v_r_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Nat_digitChar(v_n_1593_);
    crate::leanh::lean_dec(v_n_1593_);
    v_r_1595_ = crate::leanh::lean_box_uint32(v_res_1594_);
    return v_r_1595_;
}
pub unsafe fn l_Nat_toDigitsCore(
    mut v_base_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
    mut v_x_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1601_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1603_: u32 = 0;
    let mut v_n_x27_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v_one_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1600_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_1601_ = lean_nat_dec_eq(v_x_1597_, v_zero_1600_);
                if v_isZero_1601_ == 1 {
                    crate::leanh::lean_dec(v_x_1598_);
                    crate::leanh::lean_dec(v_x_1597_);
                    return v_x_1599_;
                } else {
                    v___x_1602_ = lean_nat_mod(v_x_1598_, v_base_1596_);
                    v_d_1603_ = l_Nat_digitChar(v___x_1602_);
                    crate::leanh::lean_dec(v___x_1602_);
                    v_n_x27_1604_ = lean_nat_div(v_x_1598_, v_base_1596_);
                    crate::leanh::lean_dec(v_x_1598_);
                    v___x_1605_ = lean_nat_dec_eq(v_n_x27_1604_, v_zero_1600_);
                    if v___x_1605_ == 0 {
                        v_one_1606_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_1607_ = lean_nat_sub(v_x_1597_, v_one_1606_);
                        crate::leanh::lean_dec(v_x_1597_);
                        v___x_1608_ = crate::leanh::lean_box_uint32(v_d_1603_);
                        v___x_1609_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
                        crate::leanh::lean_ctor_set(v___x_1609_, 1, v_x_1599_);
                        v_x_1597_ = v_n_1607_;
                        v_x_1598_ = v_n_x27_1604_;
                        v_x_1599_ = v___x_1609_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_x27_1604_);
                        crate::leanh::lean_dec(v_x_1597_);
                        v___x_1611_ = crate::leanh::lean_box_uint32(v_d_1603_);
                        v___x_1612_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                        crate::leanh::lean_ctor_set(v___x_1612_, 1, v_x_1599_);
                        return v___x_1612_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toDigitsCore___boxed(
    mut v_base_1613_: *mut crate::leanh::LeanObject,
    mut v_x_1614_: *mut crate::leanh::LeanObject,
    mut v_x_1615_: *mut crate::leanh::LeanObject,
    mut v_x_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Nat_toDigitsCore(v_base_1613_, v_x_1614_, v_x_1615_, v_x_1616_);
    crate::leanh::lean_dec(v_base_1613_);
    return v_res_1617_;
}
pub unsafe fn l_Nat_toDigits(
    mut v_base_1618_: *mut crate::leanh::LeanObject,
    mut v_n_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1621_ = lean_nat_add(v_n_1619_, v___x_1620_);
    v___x_1622_ = crate::leanh::lean_box(0);
    v___x_1623_ = l_Nat_toDigitsCore(v_base_1618_, v___x_1621_, v_n_1619_, v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_Nat_toDigits___boxed(
    mut v_base_1624_: *mut crate::leanh::LeanObject,
    mut v_n_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Nat_toDigits(v_base_1624_, v_n_1625_);
    crate::leanh::lean_dec(v_base_1624_);
    return v_res_1626_;
}
pub unsafe fn l_USize_repr___boxed(
    mut v_n_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1629_: usize = 0;
    let mut v_res_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1629_ = crate::leanh::lean_unbox_usize(v_n_1628_);
    crate::leanh::lean_dec(v_n_1628_);
    v_res_1630_ = lean_string_of_usize(v_n_boxed_1629_);
    return v_res_1630_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(
    mut v_a_1631_: *mut crate::leanh::LeanObject,
    mut v_a_1632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: usize = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1631_) == 0 {
                    v___x_1633_ = l_List_reverse___redArg(v_a_1632_);
                    return v___x_1633_;
                } else {
                    v_head_1634_ = crate::leanh::lean_ctor_get(v_a_1631_, 0);
                    v_tail_1635_ = crate::leanh::lean_ctor_get(v_a_1631_, 1);
                    v_isSharedCheck_1645_ = (!crate::leanh::lean_is_exclusive(v_a_1631_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1637_ = v_a_1631_;
                        v_isShared_1638_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1635_);
                        crate::leanh::lean_inc(v_head_1634_);
                        crate::leanh::lean_dec(v_a_1631_);
                        v___x_1637_ = crate::leanh::lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1639_ = lean_usize_of_nat(v_head_1634_);
                crate::leanh::lean_dec(v_head_1634_);
                v___x_1640_ = lean_string_of_usize(v___x_1639_);
                if v_isShared_1638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1637_, 1, v_a_1632_);
                    crate::leanh::lean_ctor_set(v___x_1637_, 0, v___x_1640_);
                    v___x_1642_ = v___x_1637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1632_);
                    v___x_1642_ = v_reuseFailAlloc_1644_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1631_ = v_tail_1635_;
                v_a_1632_ = v___x_1642_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = crate::leanh::lean_unsigned_to_nat(128);
    v___x_1647_ = l_List_range(v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = crate::leanh::lean_box(0);
    v___x_1649_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__0),
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once),
        _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__0,
    );
    v___x_1650_ = l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(
        v___x_1649_,
        v___x_1648_,
    );
    return v___x_1650_;
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__1),
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once),
        _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1,
    );
    v___x_1652_ = lean_array_mk(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray() -> *mut crate::leanh::LeanObject {
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__2),
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once),
        _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2,
    );
    return v___x_1653_;
}
pub unsafe fn _init_l_Nat_reprFast___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = l___private_Init_Data_Repr_0__Nat_reprArray;
    v___x_1655_ = lean_array_get_size(v___x_1654_);
    return v___x_1655_;
}
pub unsafe fn _init_l_Nat_reprFast___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_System_Platform_numBits;
    v___x_1657_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1658_ = lean_nat_pow(v___x_1657_, v___x_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Nat_reprFast(
    mut v_n_1659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    v___x_1660_ = l___private_Init_Data_Repr_0__Nat_reprArray;
    v___x_1661_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_reprFast___closed__0),
        core::ptr::addr_of_mut!(l_Nat_reprFast___closed__0_once),
        _init_l_Nat_reprFast___closed__0,
    );
    v___x_1662_ = lean_nat_dec_lt(v_n_1659_, v___x_1661_);
    if v___x_1662_ == 0 {
        let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: u8 = 0;
        v___x_1663_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Nat_reprFast___closed__1),
            core::ptr::addr_of_mut!(l_Nat_reprFast___closed__1_once),
            _init_l_Nat_reprFast___closed__1,
        );
        v___x_1664_ = lean_nat_dec_lt(v_n_1659_, v___x_1663_);
        if v___x_1664_ == 0 {
            let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1665_ = crate::leanh::lean_unsigned_to_nat(10);
            v___x_1666_ = l_Nat_toDigits(v___x_1665_, v_n_1659_);
            v___x_1667_ = lean_string_mk(v___x_1666_);
            return v___x_1667_;
        } else {
            let mut v___x_1668_: usize = 0;
            let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1668_ = lean_usize_of_nat(v_n_1659_);
            crate::leanh::lean_dec(v_n_1659_);
            v___x_1669_ = lean_string_of_usize(v___x_1668_);
            return v___x_1669_;
        }
    } else {
        let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1670_ = lean_array_fget_borrowed(v___x_1660_, v_n_1659_);
        crate::leanh::lean_dec(v_n_1659_);
        crate::leanh::lean_inc(v___x_1670_);
        return v___x_1670_;
    }
}
pub unsafe fn l_Nat_superDigitChar(mut v_n_1671_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    v___x_1672_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1673_ = lean_nat_dec_eq(v_n_1671_, v___x_1672_);
    if v___x_1673_ == 0 {
        let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: u8 = 0;
        v___x_1674_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1675_ = lean_nat_dec_eq(v_n_1671_, v___x_1674_);
        if v___x_1675_ == 0 {
            let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1677_: u8 = 0;
            v___x_1676_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_1677_ = lean_nat_dec_eq(v_n_1671_, v___x_1676_);
            if v___x_1677_ == 0 {
                let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1679_: u8 = 0;
                v___x_1678_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1679_ = lean_nat_dec_eq(v_n_1671_, v___x_1678_);
                if v___x_1679_ == 0 {
                    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1681_: u8 = 0;
                    v___x_1680_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1681_ = lean_nat_dec_eq(v_n_1671_, v___x_1680_);
                    if v___x_1681_ == 0 {
                        let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1683_: u8 = 0;
                        v___x_1682_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_1683_ = lean_nat_dec_eq(v_n_1671_, v___x_1682_);
                        if v___x_1683_ == 0 {
                            let mut v___x_1684_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1685_: u8 = 0;
                            v___x_1684_ = crate::leanh::lean_unsigned_to_nat(6);
                            v___x_1685_ = lean_nat_dec_eq(v_n_1671_, v___x_1684_);
                            if v___x_1685_ == 0 {
                                let mut v___x_1686_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1687_: u8 = 0;
                                v___x_1686_ = crate::leanh::lean_unsigned_to_nat(7);
                                v___x_1687_ = lean_nat_dec_eq(v_n_1671_, v___x_1686_);
                                if v___x_1687_ == 0 {
                                    let mut v___x_1688_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1689_: u8 = 0;
                                    v___x_1688_ = crate::leanh::lean_unsigned_to_nat(8);
                                    v___x_1689_ = lean_nat_dec_eq(v_n_1671_, v___x_1688_);
                                    if v___x_1689_ == 0 {
                                        let mut v___x_1690_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1691_: u8 = 0;
                                        v___x_1690_ = crate::leanh::lean_unsigned_to_nat(9);
                                        v___x_1691_ = lean_nat_dec_eq(v_n_1671_, v___x_1690_);
                                        if v___x_1691_ == 0 {
                                            let mut v___x_1692_: u32 = 0;
                                            v___x_1692_ = 42;
                                            return v___x_1692_;
                                        } else {
                                            let mut v___x_1693_: u32 = 0;
                                            v___x_1693_ = 8313;
                                            return v___x_1693_;
                                        }
                                    } else {
                                        let mut v___x_1694_: u32 = 0;
                                        v___x_1694_ = 8312;
                                        return v___x_1694_;
                                    }
                                } else {
                                    let mut v___x_1695_: u32 = 0;
                                    v___x_1695_ = 8311;
                                    return v___x_1695_;
                                }
                            } else {
                                let mut v___x_1696_: u32 = 0;
                                v___x_1696_ = 8310;
                                return v___x_1696_;
                            }
                        } else {
                            let mut v___x_1697_: u32 = 0;
                            v___x_1697_ = 8309;
                            return v___x_1697_;
                        }
                    } else {
                        let mut v___x_1698_: u32 = 0;
                        v___x_1698_ = 8308;
                        return v___x_1698_;
                    }
                } else {
                    let mut v___x_1699_: u32 = 0;
                    v___x_1699_ = 179;
                    return v___x_1699_;
                }
            } else {
                let mut v___x_1700_: u32 = 0;
                v___x_1700_ = 178;
                return v___x_1700_;
            }
        } else {
            let mut v___x_1701_: u32 = 0;
            v___x_1701_ = 185;
            return v___x_1701_;
        }
    } else {
        let mut v___x_1702_: u32 = 0;
        v___x_1702_ = 8304;
        return v___x_1702_;
    }
}
pub unsafe fn l_Nat_superDigitChar___boxed(
    mut v_n_1703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1704_: u32 = 0;
    let mut v_r_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Nat_superDigitChar(v_n_1703_);
    crate::leanh::lean_dec(v_n_1703_);
    v_r_1705_ = crate::leanh::lean_box_uint32(v_res_1704_);
    return v_r_1705_;
}
pub unsafe fn l_Nat_toSuperDigitsAux(
    mut v_x_1706_: *mut crate::leanh::LeanObject,
    mut v_x_1707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1710_: u32 = 0;
    let mut v_n_x27_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1708_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1709_ = lean_nat_mod(v_x_1706_, v___x_1708_);
                v_d_1710_ = l_Nat_superDigitChar(v___x_1709_);
                crate::leanh::lean_dec(v___x_1709_);
                v_n_x27_1711_ = lean_nat_div(v_x_1706_, v___x_1708_);
                crate::leanh::lean_dec(v_x_1706_);
                v___x_1712_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1713_ = lean_nat_dec_eq(v_n_x27_1711_, v___x_1712_);
                if v___x_1713_ == 0 {
                    v___x_1714_ = crate::leanh::lean_box_uint32(v_d_1710_);
                    v___x_1715_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                    crate::leanh::lean_ctor_set(v___x_1715_, 1, v_x_1707_);
                    v_x_1706_ = v_n_x27_1711_;
                    v_x_1707_ = v___x_1715_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_x27_1711_);
                    v___x_1717_ = crate::leanh::lean_box_uint32(v_d_1710_);
                    v___x_1718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
                    crate::leanh::lean_ctor_set(v___x_1718_, 1, v_x_1707_);
                    return v___x_1718_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toSuperDigits(
    mut v_n_1719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = crate::leanh::lean_box(0);
    v___x_1721_ = l_Nat_toSuperDigitsAux(v_n_1719_, v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Nat_toSuperscriptString(
    mut v_n_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Nat_toSuperDigits(v_n_1722_);
    v___x_1724_ = lean_string_mk(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Nat_subDigitChar(mut v_n_1725_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    v___x_1726_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1727_ = lean_nat_dec_eq(v_n_1725_, v___x_1726_);
    if v___x_1727_ == 0 {
        let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: u8 = 0;
        v___x_1728_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1729_ = lean_nat_dec_eq(v_n_1725_, v___x_1728_);
        if v___x_1729_ == 0 {
            let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1731_: u8 = 0;
            v___x_1730_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_1731_ = lean_nat_dec_eq(v_n_1725_, v___x_1730_);
            if v___x_1731_ == 0 {
                let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1733_: u8 = 0;
                v___x_1732_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1733_ = lean_nat_dec_eq(v_n_1725_, v___x_1732_);
                if v___x_1733_ == 0 {
                    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1735_: u8 = 0;
                    v___x_1734_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1735_ = lean_nat_dec_eq(v_n_1725_, v___x_1734_);
                    if v___x_1735_ == 0 {
                        let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1737_: u8 = 0;
                        v___x_1736_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_1737_ = lean_nat_dec_eq(v_n_1725_, v___x_1736_);
                        if v___x_1737_ == 0 {
                            let mut v___x_1738_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1739_: u8 = 0;
                            v___x_1738_ = crate::leanh::lean_unsigned_to_nat(6);
                            v___x_1739_ = lean_nat_dec_eq(v_n_1725_, v___x_1738_);
                            if v___x_1739_ == 0 {
                                let mut v___x_1740_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1741_: u8 = 0;
                                v___x_1740_ = crate::leanh::lean_unsigned_to_nat(7);
                                v___x_1741_ = lean_nat_dec_eq(v_n_1725_, v___x_1740_);
                                if v___x_1741_ == 0 {
                                    let mut v___x_1742_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1743_: u8 = 0;
                                    v___x_1742_ = crate::leanh::lean_unsigned_to_nat(8);
                                    v___x_1743_ = lean_nat_dec_eq(v_n_1725_, v___x_1742_);
                                    if v___x_1743_ == 0 {
                                        let mut v___x_1744_: *mut crate::leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1745_: u8 = 0;
                                        v___x_1744_ = crate::leanh::lean_unsigned_to_nat(9);
                                        v___x_1745_ = lean_nat_dec_eq(v_n_1725_, v___x_1744_);
                                        if v___x_1745_ == 0 {
                                            let mut v___x_1746_: u32 = 0;
                                            v___x_1746_ = 42;
                                            return v___x_1746_;
                                        } else {
                                            let mut v___x_1747_: u32 = 0;
                                            v___x_1747_ = 8329;
                                            return v___x_1747_;
                                        }
                                    } else {
                                        let mut v___x_1748_: u32 = 0;
                                        v___x_1748_ = 8328;
                                        return v___x_1748_;
                                    }
                                } else {
                                    let mut v___x_1749_: u32 = 0;
                                    v___x_1749_ = 8327;
                                    return v___x_1749_;
                                }
                            } else {
                                let mut v___x_1750_: u32 = 0;
                                v___x_1750_ = 8326;
                                return v___x_1750_;
                            }
                        } else {
                            let mut v___x_1751_: u32 = 0;
                            v___x_1751_ = 8325;
                            return v___x_1751_;
                        }
                    } else {
                        let mut v___x_1752_: u32 = 0;
                        v___x_1752_ = 8324;
                        return v___x_1752_;
                    }
                } else {
                    let mut v___x_1753_: u32 = 0;
                    v___x_1753_ = 8323;
                    return v___x_1753_;
                }
            } else {
                let mut v___x_1754_: u32 = 0;
                v___x_1754_ = 8322;
                return v___x_1754_;
            }
        } else {
            let mut v___x_1755_: u32 = 0;
            v___x_1755_ = 8321;
            return v___x_1755_;
        }
    } else {
        let mut v___x_1756_: u32 = 0;
        v___x_1756_ = 8320;
        return v___x_1756_;
    }
}
pub unsafe fn l_Nat_subDigitChar___boxed(
    mut v_n_1757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1758_: u32 = 0;
    let mut v_r_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l_Nat_subDigitChar(v_n_1757_);
    crate::leanh::lean_dec(v_n_1757_);
    v_r_1759_ = crate::leanh::lean_box_uint32(v_res_1758_);
    return v_r_1759_;
}
pub unsafe fn l_Nat_toSubDigitsAux(
    mut v_x_1760_: *mut crate::leanh::LeanObject,
    mut v_x_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1764_: u32 = 0;
    let mut v_n_x27_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1762_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_1763_ = lean_nat_mod(v_x_1760_, v___x_1762_);
                v_d_1764_ = l_Nat_subDigitChar(v___x_1763_);
                crate::leanh::lean_dec(v___x_1763_);
                v_n_x27_1765_ = lean_nat_div(v_x_1760_, v___x_1762_);
                crate::leanh::lean_dec(v_x_1760_);
                v___x_1766_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1767_ = lean_nat_dec_eq(v_n_x27_1765_, v___x_1766_);
                if v___x_1767_ == 0 {
                    v___x_1768_ = crate::leanh::lean_box_uint32(v_d_1764_);
                    v___x_1769_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 1, v_x_1761_);
                    v_x_1760_ = v_n_x27_1765_;
                    v_x_1761_ = v___x_1769_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_x27_1765_);
                    v___x_1771_ = crate::leanh::lean_box_uint32(v_d_1764_);
                    v___x_1772_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                    crate::leanh::lean_ctor_set(v___x_1772_, 1, v_x_1761_);
                    return v___x_1772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toSubDigits(
    mut v_n_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = crate::leanh::lean_box(0);
    v___x_1775_ = l_Nat_toSubDigitsAux(v_n_1773_, v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Nat_toSubscriptString(
    mut v_n_1776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Nat_toSubDigits(v_n_1776_);
    v___x_1778_ = lean_string_mk(v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_instReprNat___lam__0(
    mut v_n_1779_: *mut crate::leanh::LeanObject,
    mut v_x_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Nat_reprFast(v_n_1779_);
    v___x_1782_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l_instReprNat___lam__0___boxed(
    mut v_n_1783_: *mut crate::leanh::LeanObject,
    mut v_x_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_instReprNat___lam__0(v_n_1783_, v_x_1784_);
    crate::leanh::lean_dec(v_x_1784_);
    return v_res_1785_;
}
pub unsafe fn l_hexDigitRepr(
    mut v_n_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1790_: u32 = 0;
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Nat_digitChar(v_n_1789_);
    v___x_1791_ = l_hexDigitRepr___closed__0;
    v___x_1792_ = lean_string_push(v___x_1791_, v___x_1790_);
    return v___x_1792_;
}
pub unsafe fn l_hexDigitRepr___boxed(
    mut v_n_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_hexDigitRepr(v_n_1793_);
    crate::leanh::lean_dec(v_n_1793_);
    return v_res_1794_;
}
pub unsafe fn l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(
    mut v_c_1795_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d2_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_d1_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_1796_ = lean_uint32_to_nat(v_c_1795_);
    v___x_1797_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1798_ = crate::leanh::lean_unsigned_to_nat(4);
    v_d2_1799_ = lean_nat_shiftr(v_n_1796_, v___x_1798_);
    v_d1_1800_ = lean_nat_mod(v_n_1796_, v___x_1797_);
    crate::leanh::lean_dec(v_n_1796_);
    v___x_1801_ = l_hexDigitRepr(v_d2_1799_);
    crate::leanh::lean_dec(v_d2_1799_);
    v___x_1802_ = l_hexDigitRepr(v_d1_1800_);
    crate::leanh::lean_dec(v_d1_1800_);
    v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
    crate::leanh::lean_dec_ref(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(
    mut v_c_1804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1805_: u32 = 0;
    let mut v_res_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1805_ = crate::leanh::lean_unbox_uint32(v_c_1804_);
    crate::leanh::lean_dec(v_c_1804_);
    v_res_1806_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_boxed_1805_);
    return v_res_1806_;
}
pub unsafe fn l_Char_quoteCore(
    mut v_c_1813_: u32,
    mut v_inString_1814_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: u32 = 0;
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u32 = 0;
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: u32 = 0;
    let mut v___x_1830_: u8 = 0;
    let mut v___x_1831_: u32 = 0;
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: u32 = 0;
    let mut v___x_1834_: u8 = 0;
    let mut v___x_1835_: u32 = 0;
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1827_ = 10;
                v___x_1828_ = lean_uint32_dec_eq(v_c_1813_, v___x_1827_);
                if v___x_1828_ == 0 {
                    v___x_1829_ = 9;
                    v___x_1830_ = lean_uint32_dec_eq(v_c_1813_, v___x_1829_);
                    if v___x_1830_ == 0 {
                        v___x_1831_ = 92;
                        v___x_1832_ = lean_uint32_dec_eq(v_c_1813_, v___x_1831_);
                        if v___x_1832_ == 0 {
                            v___x_1833_ = 34;
                            v___x_1834_ = lean_uint32_dec_eq(v_c_1813_, v___x_1833_);
                            if v___x_1834_ == 0 {
                                if v_inString_1814_ == 0 {
                                    v___x_1835_ = 39;
                                    v___x_1836_ = lean_uint32_dec_eq(v_c_1813_, v___x_1835_);
                                    if v___x_1836_ == 0 {
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_1837_ = l_Char_quoteCore___closed__1;
                                        return v___x_1837_;
                                    }
                                } else {
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___x_1838_ = l_Char_quoteCore___closed__2;
                                return v___x_1838_;
                            }
                        } else {
                            v___x_1839_ = l_Char_quoteCore___closed__3;
                            return v___x_1839_;
                        }
                    } else {
                        v___x_1840_ = l_Char_quoteCore___closed__4;
                        return v___x_1840_;
                    }
                } else {
                    v___x_1841_ = l_Char_quoteCore___closed__5;
                    return v___x_1841_;
                }
            }
            1 => {
                v___x_1816_ = l_Char_quoteCore___closed__0;
                v___x_1817_ =
                    l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_1813_);
                v___x_1818_ = lean_string_append(v___x_1816_, v___x_1817_);
                crate::leanh::lean_dec_ref(v___x_1817_);
                return v___x_1818_;
            }
            2 => {
                v___x_1820_ = lean_uint32_to_nat(v_c_1813_);
                v___x_1821_ = crate::leanh::lean_unsigned_to_nat(31);
                v___x_1822_ = lean_nat_dec_le(v___x_1820_, v___x_1821_);
                crate::leanh::lean_dec(v___x_1820_);
                if v___x_1822_ == 0 {
                    v___x_1823_ = 127;
                    v___x_1824_ = lean_uint32_dec_eq(v_c_1813_, v___x_1823_);
                    if v___x_1824_ == 0 {
                        v___x_1825_ = l_hexDigitRepr___closed__0;
                        v___x_1826_ = lean_string_push(v___x_1825_, v_c_1813_);
                        return v___x_1826_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_quoteCore___boxed(
    mut v_c_1842_: *mut crate::leanh::LeanObject,
    mut v_inString_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1844_: u32 = 0;
    let mut v_inString_boxed_1845_: u8 = 0;
    let mut v_res_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1844_ = crate::leanh::lean_unbox_uint32(v_c_1842_);
    crate::leanh::lean_dec(v_c_1842_);
    v_inString_boxed_1845_ = (crate::leanh::lean_unbox(v_inString_1843_) as u8);
    v_res_1846_ = l_Char_quoteCore(v_c_boxed_1844_, v_inString_boxed_1845_);
    return v_res_1846_;
}
pub unsafe fn l_Char_quote(mut v_c_1848_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Char_quote___closed__0;
    v___x_1850_ = 0;
    v___x_1851_ = l_Char_quoteCore(v_c_1848_, v___x_1850_);
    v___x_1852_ = lean_string_append(v___x_1849_, v___x_1851_);
    crate::leanh::lean_dec_ref(v___x_1851_);
    v___x_1853_ = lean_string_append(v___x_1852_, v___x_1849_);
    return v___x_1853_;
}
pub unsafe fn l_Char_quote___boxed(
    mut v_c_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1855_: u32 = 0;
    let mut v_res_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1855_ = crate::leanh::lean_unbox_uint32(v_c_1854_);
    crate::leanh::lean_dec(v_c_1854_);
    v_res_1856_ = l_Char_quote(v_c_boxed_1855_);
    return v_res_1856_;
}
pub unsafe fn l_instReprChar___lam__0(
    mut v_c_1857_: u32,
    mut v_x_1858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Char_quote(v_c_1857_);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_instReprChar___lam__0___boxed(
    mut v_c_1861_: *mut crate::leanh::LeanObject,
    mut v_x_1862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1863_: u32 = 0;
    let mut v_res_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1863_ = crate::leanh::lean_unbox_uint32(v_c_1861_);
    crate::leanh::lean_dec(v_c_1861_);
    v_res_1864_ = l_instReprChar___lam__0(v_c_boxed_1863_, v_x_1862_);
    crate::leanh::lean_dec(v_x_1862_);
    return v_res_1864_;
}
pub unsafe fn l_Char_repr(mut v_c_1867_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Char_quote(v_c_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Char_repr___boxed(
    mut v_c_1869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_1870_: u32 = 0;
    let mut v_res_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1870_ = crate::leanh::lean_unbox_uint32(v_c_1869_);
    crate::leanh::lean_dec(v_c_1869_);
    v_res_1871_ = l_Char_repr(v_c_boxed_1870_);
    return v_res_1871_;
}
pub unsafe fn l_String_quote___lam__0(
    mut v___x_1872_: u8,
    mut v_s_1873_: *mut crate::leanh::LeanObject,
    mut v_c_1874_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Char_quoteCore(v_c_1874_, v___x_1872_);
    v___x_1876_ = lean_string_append(v_s_1873_, v___x_1875_);
    crate::leanh::lean_dec_ref(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_String_quote___lam__0___boxed(
    mut v___x_1877_: *mut crate::leanh::LeanObject,
    mut v_s_1878_: *mut crate::leanh::LeanObject,
    mut v_c_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_43__boxed_1880_: u8 = 0;
    let mut v_c_boxed_1881_: u32 = 0;
    let mut v_res_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_43__boxed_1880_ = (crate::leanh::lean_unbox(v___x_1877_) as u8);
    v_c_boxed_1881_ = crate::leanh::lean_unbox_uint32(v_c_1879_);
    crate::leanh::lean_dec(v_c_1879_);
    v_res_1882_ = l_String_quote___lam__0(v___x_43__boxed_1880_, v_s_1878_, v_c_boxed_1881_);
    return v_res_1882_;
}
pub unsafe fn l_String_quote(
    mut v_s_1888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: u8 = 0;
    crate::leanh::lean_inc_ref(v_s_1888_);
    v___x_1889_ = lean_string_isempty(v_s_1888_);
    if v___x_1889_ == 0 {
        let mut v___f_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___f_1890_ = l_String_quote___closed__0;
        v___x_1891_ = l_String_quote___closed__1;
        v___x_1892_ = lean_string_foldl(v___f_1890_, v___x_1891_, v_s_1888_);
        v___x_1893_ = lean_string_append(v___x_1892_, v___x_1891_);
        return v___x_1893_;
    } else {
        let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_s_1888_);
        v___x_1894_ = l_String_quote___closed__2;
        return v___x_1894_;
    }
}
pub unsafe fn l_instReprString___lam__0(
    mut v_s_1895_: *mut crate::leanh::LeanObject,
    mut v_x_1896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_String_quote(v_s_1895_);
    v___x_1898_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_instReprString___lam__0___boxed(
    mut v_s_1899_: *mut crate::leanh::LeanObject,
    mut v_x_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_instReprString___lam__0(v_s_1899_, v_x_1900_);
    crate::leanh::lean_dec(v_x_1900_);
    return v_res_1901_;
}
pub unsafe fn l_instReprRaw___lam__0(
    mut v_p_1910_: *mut crate::leanh::LeanObject,
    mut v_x_1911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_instReprRaw___lam__0___closed__1;
    v___x_1913_ = l_Nat_reprFast(v_p_1910_);
    v___x_1914_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    v___x_1915_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1915_, 0, v___x_1912_);
    crate::leanh::lean_ctor_set(v___x_1915_, 1, v___x_1914_);
    v___x_1916_ = l_instReprRaw___lam__0___closed__3;
    v___x_1917_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1917_, 0, v___x_1915_);
    crate::leanh::lean_ctor_set(v___x_1917_, 1, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_instReprRaw___lam__0___boxed(
    mut v_p_1918_: *mut crate::leanh::LeanObject,
    mut v_x_1919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_instReprRaw___lam__0(v_p_1918_, v_x_1919_);
    crate::leanh::lean_dec(v_x_1919_);
    return v_res_1920_;
}
pub unsafe fn l_instReprRaw__1___lam__0(
    mut v_s_1924_: *mut crate::leanh::LeanObject,
    mut v_x_1925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = lean_substring_tostring(v_s_1924_);
    v___x_1927_ = l_String_quote(v___x_1926_);
    v___x_1928_ = l_instReprRaw__1___lam__0___closed__0;
    v___x_1929_ = lean_string_append(v___x_1927_, v___x_1928_);
    v___x_1930_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn l_instReprRaw__1___lam__0___boxed(
    mut v_s_1931_: *mut crate::leanh::LeanObject,
    mut v_x_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_instReprRaw__1___lam__0(v_s_1931_, v_x_1932_);
    crate::leanh::lean_dec(v_x_1932_);
    return v_res_1933_;
}
pub unsafe fn l_instReprFin___lam__0(
    mut v_f_1936_: *mut crate::leanh::LeanObject,
    mut v_x_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Nat_reprFast(v_f_1936_);
    v___x_1939_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
    return v___x_1939_;
}
pub unsafe fn l_instReprFin___lam__0___boxed(
    mut v_f_1940_: *mut crate::leanh::LeanObject,
    mut v_x_1941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_instReprFin___lam__0(v_f_1940_, v_x_1941_);
    crate::leanh::lean_dec(v_x_1941_);
    return v_res_1942_;
}
pub unsafe fn l_instReprFin(
    mut v_n_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1945_ = l_instReprFin___closed__0;
    return v___f_1945_;
}
pub unsafe fn l_instReprFin___boxed(
    mut v_n_1946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_instReprFin(v_n_1946_);
    crate::leanh::lean_dec(v_n_1946_);
    return v_res_1947_;
}
pub unsafe fn l_instReprUInt8___lam__0(
    mut v_n_1948_: u8,
    mut v_x_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_uint8_to_nat(v_n_1948_);
    v___x_1951_ = l_Nat_reprFast(v___x_1950_);
    v___x_1952_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1952_, 0, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_instReprUInt8___lam__0___boxed(
    mut v_n_1953_: *mut crate::leanh::LeanObject,
    mut v_x_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1955_: u8 = 0;
    let mut v_res_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1955_ = (crate::leanh::lean_unbox(v_n_1953_) as u8);
    v_res_1956_ = l_instReprUInt8___lam__0(v_n_boxed_1955_, v_x_1954_);
    crate::leanh::lean_dec(v_x_1954_);
    return v_res_1956_;
}
pub unsafe fn l_instReprUInt16___lam__0(
    mut v_n_1959_: u16,
    mut v_x_1960_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = lean_uint16_to_nat(v_n_1959_);
    v___x_1962_ = l_Nat_reprFast(v___x_1961_);
    v___x_1963_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn l_instReprUInt16___lam__0___boxed(
    mut v_n_1964_: *mut crate::leanh::LeanObject,
    mut v_x_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1966_: u16 = 0;
    let mut v_res_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1966_ = (crate::leanh::lean_unbox(v_n_1964_) as u16);
    v_res_1967_ = l_instReprUInt16___lam__0(v_n_boxed_1966_, v_x_1965_);
    crate::leanh::lean_dec(v_x_1965_);
    return v_res_1967_;
}
pub unsafe fn l_instReprUInt32___lam__0(
    mut v_n_1970_: u32,
    mut v_x_1971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = lean_uint32_to_nat(v_n_1970_);
    v___x_1973_ = l_Nat_reprFast(v___x_1972_);
    v___x_1974_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1974_, 0, v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn l_instReprUInt32___lam__0___boxed(
    mut v_n_1975_: *mut crate::leanh::LeanObject,
    mut v_x_1976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1977_: u32 = 0;
    let mut v_res_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1977_ = crate::leanh::lean_unbox_uint32(v_n_1975_);
    crate::leanh::lean_dec(v_n_1975_);
    v_res_1978_ = l_instReprUInt32___lam__0(v_n_boxed_1977_, v_x_1976_);
    crate::leanh::lean_dec(v_x_1976_);
    return v_res_1978_;
}
pub unsafe fn l_instReprUInt64___lam__0(
    mut v_n_1981_: u64,
    mut v_x_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = lean_uint64_to_nat(v_n_1981_);
    v___x_1984_ = l_Nat_reprFast(v___x_1983_);
    v___x_1985_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    return v___x_1985_;
}
pub unsafe fn l_instReprUInt64___lam__0___boxed(
    mut v_n_1986_: *mut crate::leanh::LeanObject,
    mut v_x_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1988_: u64 = 0;
    let mut v_res_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1988_ = crate::leanh::lean_unbox_uint64(v_n_1986_);
    crate::leanh::lean_dec_ref(v_n_1986_);
    v_res_1989_ = l_instReprUInt64___lam__0(v_n_boxed_1988_, v_x_1987_);
    crate::leanh::lean_dec(v_x_1987_);
    return v_res_1989_;
}
pub unsafe fn l_instReprUSize___lam__0(
    mut v_n_1992_: usize,
    mut v_x_1993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_usize_to_nat(v_n_1992_);
    v___x_1995_ = l_Nat_reprFast(v___x_1994_);
    v___x_1996_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1996_, 0, v___x_1995_);
    return v___x_1996_;
}
pub unsafe fn l_instReprUSize___lam__0___boxed(
    mut v_n_1997_: *mut crate::leanh::LeanObject,
    mut v_x_1998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_1999_: usize = 0;
    let mut v_res_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1999_ = crate::leanh::lean_unbox_usize(v_n_1997_);
    crate::leanh::lean_dec(v_n_1997_);
    v_res_2000_ = l_instReprUSize___lam__0(v_n_boxed_1999_, v_x_1998_);
    crate::leanh::lean_dec(v_x_1998_);
    return v_res_2000_;
}
pub unsafe fn _init_l_List_repr___redArg___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_List_repr___redArg___closed__2;
    v___x_2009_ = lean_string_length(v___x_2008_);
    return v___x_2009_;
}
pub unsafe fn _init_l_List_repr___redArg___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2010_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_List_repr___redArg___closed__4_once),
        _init_l_List_repr___redArg___closed__4,
    );
    v___x_2011_ = lean_nat_to_int(v___x_2010_);
    return v___x_2011_;
}
pub unsafe fn l_List_repr___redArg(
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_a_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_2017_) == 0 {
        let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2016_);
        v___x_2018_ = l_List_repr___redArg___closed__1;
        return v___x_2018_;
    } else {
        let mut v_x_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: u8 = 0;
        let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_2019_ = crate::leanh::lean_alloc_closure(l_repr as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v_x_2019_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v_x_2019_, 1, v_inst_2016_);
        v___x_2020_ = l_Prod_repr___redArg___closed__3;
        v___x_2021_ = l_Std_Format_joinSep___redArg(v_x_2019_, v_a_2017_, v___x_2020_);
        v___x_2022_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5),
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5_once),
            _init_l_List_repr___redArg___closed__5,
        );
        v___x_2023_ = l_List_repr___redArg___closed__6;
        v___x_2024_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2024_, 0, v___x_2023_);
        crate::leanh::lean_ctor_set(v___x_2024_, 1, v___x_2021_);
        v___x_2025_ = l_List_repr___redArg___closed__7;
        v___x_2026_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2026_, 0, v___x_2024_);
        crate::leanh::lean_ctor_set(v___x_2026_, 1, v___x_2025_);
        v___x_2027_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2027_, 0, v___x_2022_);
        crate::leanh::lean_ctor_set(v___x_2027_, 1, v___x_2026_);
        v___x_2028_ = 0;
        v___x_2029_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
        crate::leanh::lean_ctor_set(v___x_2029_, 0, v___x_2027_);
        crate::leanh::lean_ctor_set_uint8(
            v___x_2029_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
            v___x_2028_,
        );
        return v___x_2029_;
    }
}
pub unsafe fn l_List_repr(
    mut v_00_u03b1_2030_: *mut crate::leanh::LeanObject,
    mut v_inst_2031_: *mut crate::leanh::LeanObject,
    mut v_a_2032_: *mut crate::leanh::LeanObject,
    mut v_n_2033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_List_repr___redArg(v_inst_2031_, v_a_2032_);
    return v___x_2034_;
}
pub unsafe fn l_List_repr___boxed(
    mut v_00_u03b1_2035_: *mut crate::leanh::LeanObject,
    mut v_inst_2036_: *mut crate::leanh::LeanObject,
    mut v_a_2037_: *mut crate::leanh::LeanObject,
    mut v_n_2038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_List_repr(v_00_u03b1_2035_, v_inst_2036_, v_a_2037_, v_n_2038_);
    crate::leanh::lean_dec(v_n_2038_);
    return v_res_2039_;
}
pub unsafe fn l_instReprList___redArg(
    mut v_inst_2040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ =
        crate::leanh::lean_alloc_closure(l_List_repr___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2041_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2041_, 1, v_inst_2040_);
    return v___x_2041_;
}
pub unsafe fn l_instReprList(
    mut v_00_u03b1_2042_: *mut crate::leanh::LeanObject,
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ =
        crate::leanh::lean_alloc_closure(l_List_repr___boxed as *mut core::ffi::c_void, 4, 2);
    crate::leanh::lean_closure_set(v___x_2044_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2044_, 1, v_inst_2043_);
    return v___x_2044_;
}
pub unsafe fn l_List_repr_x27___redArg(
    mut v_inst_2045_: *mut crate::leanh::LeanObject,
    mut v_a_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_2046_) == 0 {
        let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_inst_2045_);
        v___x_2047_ = l_List_repr___redArg___closed__1;
        return v___x_2047_;
    } else {
        let mut v_x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_2048_ = crate::leanh::lean_alloc_closure(l_repr as *mut core::ffi::c_void, 3, 2);
        crate::leanh::lean_closure_set(v_x_2048_, 0, crate::leanh::lean_box(0));
        crate::leanh::lean_closure_set(v_x_2048_, 1, v_inst_2045_);
        v___x_2049_ = l_Prod_repr___redArg___closed__3;
        v___x_2050_ = l_Std_Format_joinSep___redArg(v_x_2048_, v_a_2046_, v___x_2049_);
        v___x_2051_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5),
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5_once),
            _init_l_List_repr___redArg___closed__5,
        );
        v___x_2052_ = l_List_repr___redArg___closed__6;
        v___x_2053_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2053_, 0, v___x_2052_);
        crate::leanh::lean_ctor_set(v___x_2053_, 1, v___x_2050_);
        v___x_2054_ = l_List_repr___redArg___closed__7;
        v___x_2055_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2055_, 0, v___x_2053_);
        crate::leanh::lean_ctor_set(v___x_2055_, 1, v___x_2054_);
        v___x_2056_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2056_, 0, v___x_2051_);
        crate::leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        v___x_2057_ = l_Std_Format_fill(v___x_2056_);
        return v___x_2057_;
    }
}
pub unsafe fn l_List_repr_x27(
    mut v_00_u03b1_2058_: *mut crate::leanh::LeanObject,
    mut v_inst_2059_: *mut crate::leanh::LeanObject,
    mut v_inst_2060_: *mut crate::leanh::LeanObject,
    mut v_a_2061_: *mut crate::leanh::LeanObject,
    mut v_n_2062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l_List_repr_x27___redArg(v_inst_2059_, v_a_2061_);
    return v___x_2063_;
}
pub unsafe fn l_List_repr_x27___boxed(
    mut v_00_u03b1_2064_: *mut crate::leanh::LeanObject,
    mut v_inst_2065_: *mut crate::leanh::LeanObject,
    mut v_inst_2066_: *mut crate::leanh::LeanObject,
    mut v_a_2067_: *mut crate::leanh::LeanObject,
    mut v_n_2068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_List_repr_x27(
        v_00_u03b1_2064_,
        v_inst_2065_,
        v_inst_2066_,
        v_a_2067_,
        v_n_2068_,
    );
    crate::leanh::lean_dec(v_n_2068_);
    return v_res_2069_;
}
pub unsafe fn l_instReprListOfReprAtom___redArg(
    mut v_inst_2070_: *mut crate::leanh::LeanObject,
    mut v_inst_2071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ =
        crate::leanh::lean_alloc_closure(l_List_repr_x27___boxed as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2072_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2072_, 1, v_inst_2070_);
    crate::leanh::lean_closure_set(v___x_2072_, 2, v_inst_2071_);
    return v___x_2072_;
}
pub unsafe fn l_instReprListOfReprAtom(
    mut v_00_u03b1_2073_: *mut crate::leanh::LeanObject,
    mut v_inst_2074_: *mut crate::leanh::LeanObject,
    mut v_inst_2075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ =
        crate::leanh::lean_alloc_closure(l_List_repr_x27___boxed as *mut core::ffi::c_void, 5, 3);
    crate::leanh::lean_closure_set(v___x_2076_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2076_, 1, v_inst_2074_);
    crate::leanh::lean_closure_set(v___x_2076_, 2, v_inst_2075_);
    return v___x_2076_;
}
pub unsafe fn _init_l_instReprAtomBool() -> *mut crate::leanh::LeanObject {
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = crate::leanh::lean_box(0);
    return v___x_2077_;
}
pub unsafe fn _init_l_instReprAtomNat() -> *mut crate::leanh::LeanObject {
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2078_ = crate::leanh::lean_box(0);
    return v___x_2078_;
}
pub unsafe fn _init_l_instReprAtomInt() -> *mut crate::leanh::LeanObject {
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = crate::leanh::lean_box(0);
    return v___x_2079_;
}
pub unsafe fn _init_l_instReprAtomChar() -> *mut crate::leanh::LeanObject {
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = crate::leanh::lean_box(0);
    return v___x_2080_;
}
pub unsafe fn _init_l_instReprAtomString() -> *mut crate::leanh::LeanObject {
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2081_ = crate::leanh::lean_box(0);
    return v___x_2081_;
}
pub unsafe fn _init_l_instReprAtomUInt8() -> *mut crate::leanh::LeanObject {
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = crate::leanh::lean_box(0);
    return v___x_2082_;
}
pub unsafe fn _init_l_instReprAtomUInt16() -> *mut crate::leanh::LeanObject {
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = crate::leanh::lean_box(0);
    return v___x_2083_;
}
pub unsafe fn _init_l_instReprAtomUInt32() -> *mut crate::leanh::LeanObject {
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = crate::leanh::lean_box(0);
    return v___x_2084_;
}
pub unsafe fn _init_l_instReprAtomUInt64() -> *mut crate::leanh::LeanObject {
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = crate::leanh::lean_box(0);
    return v___x_2085_;
}
pub unsafe fn _init_l_instReprAtomUSize() -> *mut crate::leanh::LeanObject {
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = crate::leanh::lean_box(0);
    return v___x_2086_;
}
pub unsafe fn _init_l_instReprSourceInfo_repr___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2097_ = lean_nat_to_int(v___x_2096_);
    return v___x_2097_;
}
pub unsafe fn _init_l_instReprSourceInfo_repr___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2099_ = lean_nat_to_int(v___x_2098_);
    return v___x_2099_;
}
pub unsafe fn l_instReprSourceInfo_repr(
    mut v_x_2106_: *mut crate::leanh::LeanObject,
    mut v_prec_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonical_2159_: u8 = 0;
    let mut v___y_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_2106_) {
                0 => {
                    v_leading_2115_ = crate::leanh::lean_ctor_get(v_x_2106_, 0);
                    crate::leanh::lean_inc_ref(v_leading_2115_);
                    v_pos_2116_ = crate::leanh::lean_ctor_get(v_x_2106_, 1);
                    crate::leanh::lean_inc(v_pos_2116_);
                    v_trailing_2117_ = crate::leanh::lean_ctor_get(v_x_2106_, 2);
                    crate::leanh::lean_inc_ref(v_trailing_2117_);
                    v_endPos_2118_ = crate::leanh::lean_ctor_get(v_x_2106_, 3);
                    crate::leanh::lean_inc(v_endPos_2118_);
                    crate::leanh::lean_dec_ref_known(v_x_2106_, 4);
                    v___x_2153_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2154_ = lean_nat_dec_le(v___x_2153_, v_prec_2107_);
                    if v___x_2154_ == 0 {
                        v___x_2155_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2120_ = v___x_2155_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2156_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6_once),
                            _init_l_instReprSourceInfo_repr___closed__6,
                        );
                        v___y_2120_ = v___x_2156_;
                        state = 2;
                        continue;
                    }
                }
                1 => {
                    v_pos_2157_ = crate::leanh::lean_ctor_get(v_x_2106_, 0);
                    crate::leanh::lean_inc(v_pos_2157_);
                    v_endPos_2158_ = crate::leanh::lean_ctor_get(v_x_2106_, 1);
                    crate::leanh::lean_inc(v_endPos_2158_);
                    v_canonical_2159_ = crate::leanh::lean_ctor_get_uint8(
                        v_x_2106_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_x_2106_, 2);
                    v___x_2184_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2185_ = lean_nat_dec_le(v___x_2184_, v_prec_2107_);
                    if v___x_2185_ == 0 {
                        v___x_2186_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2161_ = v___x_2186_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2187_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6_once),
                            _init_l_instReprSourceInfo_repr___closed__6,
                        );
                        v___y_2161_ = v___x_2187_;
                        state = 3;
                        continue;
                    }
                }
                _ => {
                    v___x_2188_ = crate::leanh::lean_unsigned_to_nat(1024);
                    v___x_2189_ = lean_nat_dec_le(v___x_2188_, v_prec_2107_);
                    if v___x_2189_ == 0 {
                        v___x_2190_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2109_ = v___x_2190_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2191_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__6_once),
                            _init_l_instReprSourceInfo_repr___closed__6,
                        );
                        v___y_2109_ = v___x_2191_;
                        state = 1;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2110_ = l_instReprSourceInfo_repr___closed__1;
                crate::leanh::lean_inc(v___y_2109_);
                v___x_2111_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2111_, 0, v___y_2109_);
                crate::leanh::lean_ctor_set(v___x_2111_, 1, v___x_2110_);
                v___x_2112_ = 0;
                v___x_2113_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2113_, 0, v___x_2111_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2112_,
                );
                v___x_2114_ = l_Repr_addAppParen(v___x_2113_, v_prec_2107_);
                return v___x_2114_;
            }
            2 => {
                v___x_2121_ = crate::leanh::lean_box(1);
                v___x_2122_ = l_instReprSourceInfo_repr___closed__4;
                v___x_2123_ = lean_substring_tostring(v_leading_2115_);
                v___x_2124_ = l_String_quote(v___x_2123_);
                v___x_2125_ = l_instReprRaw__1___lam__0___closed__0;
                v___x_2126_ = lean_string_append(v___x_2124_, v___x_2125_);
                v___x_2127_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2127_, 0, v___x_2126_);
                v___x_2128_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2128_, 0, v___x_2122_);
                crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                v___x_2129_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2129_, 0, v___x_2128_);
                crate::leanh::lean_ctor_set(v___x_2129_, 1, v___x_2121_);
                v___x_2130_ = l_instReprRaw___lam__0___closed__1;
                v___x_2131_ = l_Nat_reprFast(v_pos_2116_);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                v___x_2133_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2133_, 0, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                v___x_2134_ = l_instReprRaw___lam__0___closed__3;
                v___x_2135_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2135_, 0, v___x_2133_);
                crate::leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                v___x_2136_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2129_);
                crate::leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
                v___x_2137_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
                crate::leanh::lean_ctor_set(v___x_2137_, 1, v___x_2121_);
                v___x_2138_ = lean_substring_tostring(v_trailing_2117_);
                v___x_2139_ = l_String_quote(v___x_2138_);
                v___x_2140_ = lean_string_append(v___x_2139_, v___x_2125_);
                v___x_2141_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2141_, 0, v___x_2140_);
                v___x_2142_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2137_);
                crate::leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
                v___x_2143_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2143_, 1, v___x_2121_);
                v___x_2144_ = l_Nat_reprFast(v_endPos_2118_);
                v___x_2145_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2144_);
                v___x_2146_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2146_, 1, v___x_2145_);
                v___x_2147_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2134_);
                v___x_2148_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2148_, 0, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2148_, 1, v___x_2147_);
                crate::leanh::lean_inc(v___y_2120_);
                v___x_2149_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2149_, 0, v___y_2120_);
                crate::leanh::lean_ctor_set(v___x_2149_, 1, v___x_2148_);
                v___x_2150_ = 0;
                v___x_2151_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2149_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2151_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2150_,
                );
                v___x_2152_ = l_Repr_addAppParen(v___x_2151_, v_prec_2107_);
                return v___x_2152_;
            }
            3 => {
                v___x_2162_ = crate::leanh::lean_box(1);
                v___x_2163_ = l_instReprSourceInfo_repr___closed__9;
                v___x_2164_ = l_instReprRaw___lam__0___closed__1;
                v___x_2165_ = l_Nat_reprFast(v_pos_2157_);
                v___x_2166_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
                v___x_2167_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2167_, 0, v___x_2164_);
                crate::leanh::lean_ctor_set(v___x_2167_, 1, v___x_2166_);
                v___x_2168_ = l_instReprRaw___lam__0___closed__3;
                v___x_2169_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2169_, 0, v___x_2167_);
                crate::leanh::lean_ctor_set(v___x_2169_, 1, v___x_2168_);
                v___x_2170_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2170_, 0, v___x_2163_);
                crate::leanh::lean_ctor_set(v___x_2170_, 1, v___x_2169_);
                v___x_2171_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                crate::leanh::lean_ctor_set(v___x_2171_, 1, v___x_2162_);
                v___x_2172_ = l_Nat_reprFast(v_endPos_2158_);
                v___x_2173_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
                v___x_2174_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2174_, 0, v___x_2164_);
                crate::leanh::lean_ctor_set(v___x_2174_, 1, v___x_2173_);
                v___x_2175_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                crate::leanh::lean_ctor_set(v___x_2175_, 1, v___x_2168_);
                v___x_2176_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2176_, 0, v___x_2171_);
                crate::leanh::lean_ctor_set(v___x_2176_, 1, v___x_2175_);
                v___x_2177_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
                crate::leanh::lean_ctor_set(v___x_2177_, 1, v___x_2162_);
                v___x_2178_ = l_Bool_repr___redArg(v_canonical_2159_);
                v___x_2179_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2179_, 0, v___x_2177_);
                crate::leanh::lean_ctor_set(v___x_2179_, 1, v___x_2178_);
                crate::leanh::lean_inc(v___y_2161_);
                v___x_2180_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2180_, 0, v___y_2161_);
                crate::leanh::lean_ctor_set(v___x_2180_, 1, v___x_2179_);
                v___x_2181_ = 0;
                v___x_2182_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_2182_, 0, v___x_2180_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2182_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_2181_,
                );
                v___x_2183_ = l_Repr_addAppParen(v___x_2182_, v_prec_2107_);
                return v___x_2183_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_instReprSourceInfo_repr___boxed(
    mut v_x_2192_: *mut crate::leanh::LeanObject,
    mut v_prec_2193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_instReprSourceInfo_repr(v_x_2192_, v_prec_2193_);
    crate::leanh::lean_dec(v_prec_2193_);
    return v_res_2194_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Init_Data_Repr_0__Nat_reprArray =
        _init_l___private_Init_Data_Repr_0__Nat_reprArray();
    crate::leanh::lean_mark_persistent(l___private_Init_Data_Repr_0__Nat_reprArray);
    l_instReprAtomBool = _init_l_instReprAtomBool();
    crate::leanh::lean_mark_persistent(l_instReprAtomBool);
    l_instReprAtomNat = _init_l_instReprAtomNat();
    crate::leanh::lean_mark_persistent(l_instReprAtomNat);
    l_instReprAtomInt = _init_l_instReprAtomInt();
    crate::leanh::lean_mark_persistent(l_instReprAtomInt);
    l_instReprAtomChar = _init_l_instReprAtomChar();
    crate::leanh::lean_mark_persistent(l_instReprAtomChar);
    l_instReprAtomString = _init_l_instReprAtomString();
    crate::leanh::lean_mark_persistent(l_instReprAtomString);
    l_instReprAtomUInt8 = _init_l_instReprAtomUInt8();
    crate::leanh::lean_mark_persistent(l_instReprAtomUInt8);
    l_instReprAtomUInt16 = _init_l_instReprAtomUInt16();
    crate::leanh::lean_mark_persistent(l_instReprAtomUInt16);
    l_instReprAtomUInt32 = _init_l_instReprAtomUInt32();
    crate::leanh::lean_mark_persistent(l_instReprAtomUInt32);
    l_instReprAtomUInt64 = _init_l_instReprAtomUInt64();
    crate::leanh::lean_mark_persistent(l_instReprAtomUInt64);
    l_instReprAtomUSize = _init_l_instReprAtomUSize();
    crate::leanh::lean_mark_persistent(l_instReprAtomUSize);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Repr(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Format_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Id(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Repr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Repr(builtin);
}
