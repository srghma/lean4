// Lean compiler output
// Module: Init.Data.Repr
// Imports: Init.Data.Format.Basic Init.Control.Id Init.Data.UInt.BasicAux Init.Data.Char.Basic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_mk, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_pow, lean_nat_shiftr,
    lean_nat_sub, lean_nat_to_int, lean_string_append, lean_string_foldl, lean_string_isempty,
    lean_string_length, lean_string_mk, lean_string_of_usize, lean_string_push,
    lean_substring_tostring, lean_uint8_to_nat, lean_uint16_to_nat, lean_uint32_dec_eq,
    lean_uint32_to_nat, lean_uint64_to_nat, lean_usize_of_nat, lean_usize_to_nat,
};
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
pub static l_instReprEmpty___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprEmpty___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprEmpty___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprEmpty___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprEmpty: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprEmpty___closed__0_value) as *mut leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__0_value: leanh::LeanStringObject<6> =
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
static mut l_Bool_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Bool_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Bool_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__2_value: leanh::LeanStringObject<5> =
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
static mut l_Bool_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Bool_repr___redArg___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Bool_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Bool_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Bool_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_instReprBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Bool_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprBool___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_Repr_addAppParen___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [40, 0],
    };
static mut l_Repr_addAppParen___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__0_value) as *mut leanh::LeanObject;
pub static l_Repr_addAppParen___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [41, 0],
    };
static mut l_Repr_addAppParen___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__1_value) as *mut leanh::LeanObject;
static mut l_Repr_addAppParen___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Repr_addAppParen___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Repr_addAppParen___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Repr_addAppParen___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Repr_addAppParen___closed__4_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Repr_addAppParen___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Repr_addAppParen___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__4_value) as *mut leanh::LeanObject;
pub static l_Repr_addAppParen___closed__5_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Repr_addAppParen___closed__1_value)
            as *mut leanh::LeanObject],
    };
static mut l_Repr_addAppParen___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Repr_addAppParen___closed__5_value) as *mut leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Decidable_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Decidable_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Decidable_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Decidable_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Decidable_repr___redArg___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Decidable_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Decidable_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Decidable_repr___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_instReprDecidable___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_Decidable_repr___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_instReprDecidable___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprDecidable___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprPUnit___lam__0___closed__0_value: leanh::LeanStringObject<11> =
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
        m_data: [80, 85, 110, 105, 116, 46, 117, 110, 105, 116, 0],
    };
static mut l_instReprPUnit___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprPUnit___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprPUnit___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprPUnit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprPUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprPUnit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprPUnit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprPUnit___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprULift___redArg___lam__0___closed__0_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprULift___redArg___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprULift___redArg___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprULift___redArg___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprULift___redArg___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprUnit___lam__0___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [40, 41, 0],
    };
static mut l_instReprUnit___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUnit___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprUnit___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprUnit___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_instReprUnit___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUnit___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUnit___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUnit: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUnit___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_repr___redArg___closed__0_value: leanh::LeanStringObject<5> =
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
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Option_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Option_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Option_repr___redArg___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Option_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Option_repr___redArg___closed__2_value: leanh::LeanStringObject<6> =
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
        m_data: [115, 111, 109, 101, 32, 0],
    };
static mut l_Option_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Option_repr___redArg___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_Option_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Option_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Option_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Sum_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sum_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Sum_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__2_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Sum_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Sum_repr___redArg___closed__3_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sum_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_Sum_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sum_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instToFormatFormat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Prod_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [44, 0],
    };
static mut l_Prod_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Prod_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject],
    };
static mut l_Prod_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Prod_repr___redArg___closed__3_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_Prod_repr___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Prod_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Prod_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_Prod_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Prod_repr___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Sigma_repr___redArg___closed__0_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Sigma_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [44, 32, 0],
    };
static mut l_Sigma_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__2_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__1_value)
            as *mut leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__3_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Sigma_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_Sigma_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Sigma_repr___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Sigma_repr___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Sigma_repr___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Sigma_repr___redArg___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_Sigma_repr___redArg___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_Sigma_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject],
    };
static mut l_Sigma_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Sigma_repr___redArg___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Init_Data_Repr_0__Nat_reprArray___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Init_Data_Repr_0__Nat_reprArray: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Nat_reprFast___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_reprFast___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Nat_reprFast___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Nat_reprFast___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instReprNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_hexDigitRepr___closed__0_value: leanh::LeanStringObject<1> =
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
static mut l_hexDigitRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_hexDigitRepr___closed__0_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 120, 0],
    };
static mut l_Char_quoteCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__0_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__1_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 39, 0],
    };
static mut l_Char_quoteCore___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__1_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 34, 0],
    };
static mut l_Char_quoteCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__2_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__3_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 92, 0],
    };
static mut l_Char_quoteCore___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__3_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__4_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 116, 0],
    };
static mut l_Char_quoteCore___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__4_value) as *mut leanh::LeanObject;
pub static l_Char_quoteCore___closed__5_value: leanh::LeanStringObject<3> =
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
        m_data: [92, 110, 0],
    };
static mut l_Char_quoteCore___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quoteCore___closed__5_value) as *mut leanh::LeanObject;
pub static l_Char_quote___closed__0_value: leanh::LeanStringObject<2> =
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
        m_data: [39, 0],
    };
static mut l_Char_quote___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Char_quote___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprChar___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprChar___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprChar___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprChar___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprChar: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprChar___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_quote___closed__0_value: leanh::LeanClosureObject<1> =
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
        m_fun: l_String_quote___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_String_quote___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__0_value) as *mut leanh::LeanObject;
pub static l_String_quote___closed__1_value: leanh::LeanStringObject<2> =
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
        m_data: [34, 0],
    };
static mut l_String_quote___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__1_value) as *mut leanh::LeanObject;
pub static l_String_quote___closed__2_value: leanh::LeanStringObject<3> =
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
        m_data: [34, 34, 0],
    };
static mut l_String_quote___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_quote___closed__2_value) as *mut leanh::LeanObject;
pub static l_instReprString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprString___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprString___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__0_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprRaw___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprRaw___lam__0___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprRaw___lam__0___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__2_value: leanh::LeanStringObject<3> =
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
static mut l_instReprRaw___lam__0___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_instReprRaw___lam__0___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprRaw___lam__0___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprRaw___lam__0___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_instReprRaw___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprRaw___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprRaw___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprRaw: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprRaw__1___lam__0___closed__0_value: leanh::LeanStringObject<16> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprRaw__1___lam__0___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___lam__0___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprRaw__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprRaw__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprRaw__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprRaw__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprRaw__1___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprFin___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprFin___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprFin___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprFin___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUInt8___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt8___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt8___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUInt8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt8___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUInt16___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt16___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt16___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUInt16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt16___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUInt32___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt32___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt32___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUInt32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt32___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUInt64___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUInt64___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUInt64___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUInt64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUInt64___closed__0_value) as *mut leanh::LeanObject;
pub static l_instReprUSize___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprUSize___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprUSize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUSize___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprUSize: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprUSize___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___redArg___closed__0_value: leanh::LeanStringObject<3> =
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
        m_data: [91, 93, 0],
    };
static mut l_List_repr___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_List_repr___redArg___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__0_value)
            as *mut leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_repr___redArg___closed__2_value: leanh::LeanStringObject<2> =
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
        m_data: [91, 0],
    };
static mut l_List_repr___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__2_value) as *mut leanh::LeanObject;
pub static l_List_repr___redArg___closed__3_value: leanh::LeanStringObject<2> =
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
        m_data: [93, 0],
    };
static mut l_List_repr___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__3_value) as *mut leanh::LeanObject;
static mut l_List_repr___redArg___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_repr___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_List_repr___redArg___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_List_repr___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_repr___redArg___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__2_value)
            as *mut leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l_List_repr___redArg___closed__7_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(l_List_repr___redArg___closed__3_value)
            as *mut leanh::LeanObject],
    };
static mut l_List_repr___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_repr___redArg___closed__7_value) as *mut leanh::LeanObject;
pub static mut l_instReprAtomBool: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomNat: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomInt: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomChar: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomString: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt16: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt32: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUInt64: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_instReprAtomUSize: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_instReprSourceInfo_repr___closed__0_value: leanh::LeanStringObject<21> =
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
            76, 101, 97, 110, 46, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 46, 110, 111, 110,
            101, 0,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__1_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__2_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_instReprSourceInfo_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__3_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__2_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__4_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__3_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_instReprSourceInfo_repr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprSourceInfo_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_instReprSourceInfo_repr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_instReprSourceInfo_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_instReprSourceInfo_repr___closed__7_value: leanh::LeanStringObject<26> =
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
            76, 101, 97, 110, 46, 83, 111, 117, 114, 99, 101, 73, 110, 102, 111, 46, 115, 121, 110,
            116, 104, 101, 116, 105, 99, 0,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__8_value: leanh::LeanCtorObject<1> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__7_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo_repr___closed__9_value: leanh::LeanCtorObject<2> =
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
            core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__8_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_instReprSourceInfo_repr___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo_repr___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_instReprSourceInfo___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_instReprSourceInfo_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_instReprSourceInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_instReprSourceInfo: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_instReprSourceInfo___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_repr___redArg(
    mut v_inst_1099_: *mut leanh::LeanObject,
    mut v_a_1100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1101_ = leanh::lean_unsigned_to_nat(0);
    v___x_1102_ = leanh::lean_apply_2(v_inst_1099_, v_a_1100_, v___x_1101_);
    return v___x_1102_;
}
pub unsafe fn l_repr(
    mut v_00_u03b1_1103_: *mut leanh::LeanObject,
    mut v_inst_1104_: *mut leanh::LeanObject,
    mut v_a_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1106_ = leanh::lean_unsigned_to_nat(0);
    v___x_1107_ = leanh::lean_apply_2(v_inst_1104_, v_a_1105_, v___x_1106_);
    return v___x_1107_;
}
pub unsafe fn l_reprStr___redArg(
    mut v_inst_1108_: *mut leanh::LeanObject,
    mut v_a_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1110_ = leanh::lean_unsigned_to_nat(0);
    v___x_1111_ = leanh::lean_apply_2(v_inst_1108_, v_a_1109_, v___x_1110_);
    v___x_1112_ = l_Std_Format_defWidth;
    v___x_1113_ = l_Std_Format_pretty(v___x_1111_, v___x_1112_, v___x_1110_, v___x_1110_);
    return v___x_1113_;
}
pub unsafe fn l_reprStr(
    mut v_00_u03b1_1114_: *mut leanh::LeanObject,
    mut v_inst_1115_: *mut leanh::LeanObject,
    mut v_a_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1117_ = leanh::lean_unsigned_to_nat(0);
    v___x_1118_ = leanh::lean_apply_2(v_inst_1115_, v_a_1116_, v___x_1117_);
    v___x_1119_ = l_Std_Format_defWidth;
    v___x_1120_ = l_Std_Format_pretty(v___x_1118_, v___x_1119_, v___x_1117_, v___x_1117_);
    return v___x_1120_;
}
pub unsafe fn l_reprArg___redArg(
    mut v_inst_1121_: *mut leanh::LeanObject,
    mut v_a_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1124_ = leanh::lean_apply_2(v_inst_1121_, v_a_1122_, v___x_1123_);
    return v___x_1124_;
}
pub unsafe fn l_reprArg(
    mut v_00_u03b1_1125_: *mut leanh::LeanObject,
    mut v_inst_1126_: *mut leanh::LeanObject,
    mut v_a_1127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1129_ = leanh::lean_apply_2(v_inst_1126_, v_a_1127_, v___x_1128_);
    return v___x_1129_;
}
pub unsafe fn l_instReprId___aux__1___redArg(
    mut v_inst_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1130_);
    return v_inst_1130_;
}
pub unsafe fn l_instReprId___aux__1___redArg___boxed(
    mut v_inst_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l_instReprId___aux__1___redArg(v_inst_1131_);
    leanh::lean_dec_ref(v_inst_1131_);
    return v_res_1132_;
}
pub unsafe fn l_instReprId___aux__1(
    mut v_00_u03b1_1133_: *mut leanh::LeanObject,
    mut v_inst_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1134_);
    return v_inst_1134_;
}
pub unsafe fn l_instReprId___aux__1___boxed(
    mut v_00_u03b1_1135_: *mut leanh::LeanObject,
    mut v_inst_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_instReprId___aux__1(v_00_u03b1_1135_, v_inst_1136_);
    leanh::lean_dec_ref(v_inst_1136_);
    return v_res_1137_;
}
pub unsafe fn l_instReprId___redArg(
    mut v_inst_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1138_);
    return v_inst_1138_;
}
pub unsafe fn l_instReprId___redArg___boxed(
    mut v_inst_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ = l_instReprId___redArg(v_inst_1139_);
    leanh::lean_dec_ref(v_inst_1139_);
    return v_res_1140_;
}
pub unsafe fn l_instReprId(
    mut v_00_u03b1_1141_: *mut leanh::LeanObject,
    mut v_inst_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1142_);
    return v_inst_1142_;
}
pub unsafe fn l_instReprId___boxed(
    mut v_00_u03b1_1143_: *mut leanh::LeanObject,
    mut v_inst_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_instReprId(v_00_u03b1_1143_, v_inst_1144_);
    leanh::lean_dec_ref(v_inst_1144_);
    return v_res_1145_;
}
pub unsafe fn l_instReprId__1___aux__1___redArg(
    mut v_inst_1146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1146_);
    return v_inst_1146_;
}
pub unsafe fn l_instReprId__1___aux__1___redArg___boxed(
    mut v_inst_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_instReprId__1___aux__1___redArg(v_inst_1147_);
    leanh::lean_dec_ref(v_inst_1147_);
    return v_res_1148_;
}
pub unsafe fn l_instReprId__1___aux__1(
    mut v_00_u03b1_1149_: *mut leanh::LeanObject,
    mut v_inst_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1150_);
    return v_inst_1150_;
}
pub unsafe fn l_instReprId__1___aux__1___boxed(
    mut v_00_u03b1_1151_: *mut leanh::LeanObject,
    mut v_inst_1152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1153_ = l_instReprId__1___aux__1(v_00_u03b1_1151_, v_inst_1152_);
    leanh::lean_dec_ref(v_inst_1152_);
    return v_res_1153_;
}
pub unsafe fn l_instReprId__1___redArg(
    mut v_inst_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1154_);
    return v_inst_1154_;
}
pub unsafe fn l_instReprId__1___redArg___boxed(
    mut v_inst_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_instReprId__1___redArg(v_inst_1155_);
    leanh::lean_dec_ref(v_inst_1155_);
    return v_res_1156_;
}
pub unsafe fn l_instReprId__1(
    mut v_00_u03b1_1157_: *mut leanh::LeanObject,
    mut v_inst_1158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_inst_1158_);
    return v_inst_1158_;
}
pub unsafe fn l_instReprId__1___boxed(
    mut v_00_u03b1_1159_: *mut leanh::LeanObject,
    mut v_inst_1160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1161_ = l_instReprId__1(v_00_u03b1_1159_, v_inst_1160_);
    leanh::lean_dec_ref(v_inst_1160_);
    return v_res_1161_;
}
pub unsafe fn l_instReprEmpty___lam__0(
    mut v_a_1162_: u8,
    mut v_a_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    core::hint::unreachable_unchecked();
}
pub unsafe fn l_instReprEmpty___lam__0___boxed(
    mut v_a_1164_: *mut leanh::LeanObject,
    mut v_a_1165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_8__boxed_1166_: u8 = 0;
    let mut v_res_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_8__boxed_1166_ = (leanh::lean_unbox(v_a_1164_) as u8);
    v_res_1167_ = l_instReprEmpty___lam__0(v_a_8__boxed_1166_, v_a_1165_);
    leanh::lean_dec(v_a_1165_);
    return v_res_1167_;
}
pub unsafe fn l_Bool_repr___redArg(mut v_x_1176_: u8) -> *mut leanh::LeanObject {
    if v_x_1176_ == 0 {
        let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1177_ = l_Bool_repr___redArg___closed__1;
        return v___x_1177_;
    } else {
        let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1178_ = l_Bool_repr___redArg___closed__3;
        return v___x_1178_;
    }
}
pub unsafe fn l_Bool_repr___redArg___boxed(
    mut v_x_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_36__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_1180_ = (leanh::lean_unbox(v_x_1179_) as u8);
    v_res_1181_ = l_Bool_repr___redArg(v_x_36__boxed_1180_);
    return v_res_1181_;
}
pub unsafe fn l_Bool_repr(
    mut v_x_1182_: u8,
    mut v_x_1183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1184_ = l_Bool_repr___redArg(v_x_1182_);
    return v___x_1184_;
}
pub unsafe fn l_Bool_repr___boxed(
    mut v_x_1185_: *mut leanh::LeanObject,
    mut v_x_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_49__boxed_1187_: u8 = 0;
    let mut v_res_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_49__boxed_1187_ = (leanh::lean_unbox(v_x_1185_) as u8);
    v_res_1188_ = l_Bool_repr(v_x_49__boxed_1187_, v_x_1186_);
    leanh::lean_dec(v_x_1186_);
    return v_res_1188_;
}
pub unsafe fn l_Nat_cast___at___00Repr_addAppParen_spec__0(
    mut v_a_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = lean_nat_to_int(v_a_1191_);
    return v___x_1192_;
}
pub unsafe fn _init_l_Repr_addAppParen___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1195_ = l_Repr_addAppParen___closed__0;
    v___x_1196_ = lean_string_length(v___x_1195_);
    return v___x_1196_;
}
pub unsafe fn _init_l_Repr_addAppParen___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2),
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2_once),
        _init_l_Repr_addAppParen___closed__2,
    );
    v___x_1198_ = lean_nat_to_int(v___x_1197_);
    return v___x_1198_;
}
pub unsafe fn l_Repr_addAppParen(
    mut v_f_1203_: *mut leanh::LeanObject,
    mut v_prec_1204_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: u8 = 0;
    v___x_1205_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1206_ = lean_nat_dec_le(v___x_1205_, v_prec_1204_);
    if v___x_1206_ == 0 {
        return v_f_1203_;
    } else {
        let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1213_: u8 = 0;
        let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1207_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__3),
            core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__3_once),
            _init_l_Repr_addAppParen___closed__3,
        );
        v___x_1208_ = l_Repr_addAppParen___closed__4;
        v___x_1209_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1209_, 0, v___x_1208_);
        leanh::lean_ctor_set(v___x_1209_, 1, v_f_1203_);
        v___x_1210_ = l_Repr_addAppParen___closed__5;
        v___x_1211_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1211_, 0, v___x_1209_);
        leanh::lean_ctor_set(v___x_1211_, 1, v___x_1210_);
        v___x_1212_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1212_, 0, v___x_1207_);
        leanh::lean_ctor_set(v___x_1212_, 1, v___x_1211_);
        v___x_1213_ = 0;
        v___x_1214_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_1214_, 0, v___x_1212_);
        leanh::lean_ctor_set_uint8(
            v___x_1214_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_1213_,
        );
        return v___x_1214_;
    }
}
pub unsafe fn l_Repr_addAppParen___boxed(
    mut v_f_1215_: *mut leanh::LeanObject,
    mut v_prec_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ = l_Repr_addAppParen(v_f_1215_, v_prec_1216_);
    leanh::lean_dec(v_prec_1216_);
    return v_res_1217_;
}
pub unsafe fn l_Decidable_repr___redArg(
    mut v_x_1224_: u8,
    mut v_x_1225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1224_ == 0 {
        let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1226_ = l_Decidable_repr___redArg___closed__1;
        v___x_1227_ = l_Repr_addAppParen(v___x_1226_, v_x_1225_);
        return v___x_1227_;
    } else {
        let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1228_ = l_Decidable_repr___redArg___closed__3;
        v___x_1229_ = l_Repr_addAppParen(v___x_1228_, v_x_1225_);
        return v___x_1229_;
    }
}
pub unsafe fn l_Decidable_repr___redArg___boxed(
    mut v_x_1230_: *mut leanh::LeanObject,
    mut v_x_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_42__boxed_1232_: u8 = 0;
    let mut v_res_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_42__boxed_1232_ = (leanh::lean_unbox(v_x_1230_) as u8);
    v_res_1233_ = l_Decidable_repr___redArg(v_x_42__boxed_1232_, v_x_1231_);
    leanh::lean_dec(v_x_1231_);
    return v_res_1233_;
}
pub unsafe fn l_Decidable_repr(
    mut v_p_1234_: *mut leanh::LeanObject,
    mut v_x_1235_: u8,
    mut v_x_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = l_Decidable_repr___redArg(v_x_1235_, v_x_1236_);
    return v___x_1237_;
}
pub unsafe fn l_Decidable_repr___boxed(
    mut v_p_1238_: *mut leanh::LeanObject,
    mut v_x_1239_: *mut leanh::LeanObject,
    mut v_x_1240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_62__boxed_1241_: u8 = 0;
    let mut v_res_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_62__boxed_1241_ = (leanh::lean_unbox(v_x_1239_) as u8);
    v_res_1242_ = l_Decidable_repr(v_p_1238_, v_x_62__boxed_1241_, v_x_1240_);
    leanh::lean_dec(v_x_1240_);
    return v_res_1242_;
}
pub unsafe fn l_instReprDecidable(
    mut v_p_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1245_ = l_instReprDecidable___closed__0;
    return v___x_1245_;
}
pub unsafe fn l_instReprPUnit___lam__0(
    mut v_x_1249_: *mut leanh::LeanObject,
    mut v_x_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = l_instReprPUnit___lam__0___closed__1;
    return v___x_1251_;
}
pub unsafe fn l_instReprPUnit___lam__0___boxed(
    mut v_x_1252_: *mut leanh::LeanObject,
    mut v_x_1253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_instReprPUnit___lam__0(v_x_1252_, v_x_1253_);
    leanh::lean_dec(v_x_1253_);
    return v_res_1254_;
}
pub unsafe fn l_instReprULift___redArg___lam__0(
    mut v_inst_1260_: *mut leanh::LeanObject,
    mut v_v_1261_: *mut leanh::LeanObject,
    mut v_prec_1262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1263_ = l_instReprULift___redArg___lam__0___closed__1;
    v___x_1264_ = leanh::lean_unsigned_to_nat(1024);
    v___x_1265_ = leanh::lean_apply_2(v_inst_1260_, v_v_1261_, v___x_1264_);
    v___x_1266_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1263_);
    leanh::lean_ctor_set(v___x_1266_, 1, v___x_1265_);
    v___x_1267_ = l_Repr_addAppParen(v___x_1266_, v_prec_1262_);
    return v___x_1267_;
}
pub unsafe fn l_instReprULift___redArg___lam__0___boxed(
    mut v_inst_1268_: *mut leanh::LeanObject,
    mut v_v_1269_: *mut leanh::LeanObject,
    mut v_prec_1270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1271_ = l_instReprULift___redArg___lam__0(v_inst_1268_, v_v_1269_, v_prec_1270_);
    leanh::lean_dec(v_prec_1270_);
    return v_res_1271_;
}
pub unsafe fn l_instReprULift___redArg(
    mut v_inst_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1273_ = leanh::lean_alloc_closure(
        l_instReprULift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1273_, 0, v_inst_1272_);
    return v___f_1273_;
}
pub unsafe fn l_instReprULift(
    mut v_00_u03b1_1274_: *mut leanh::LeanObject,
    mut v_inst_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1276_ = leanh::lean_alloc_closure(
        l_instReprULift___redArg___lam__0___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1276_, 0, v_inst_1275_);
    return v___f_1276_;
}
pub unsafe fn l_instReprUnit___lam__0(
    mut v_x_1280_: *mut leanh::LeanObject,
    mut v_x_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = l_instReprUnit___lam__0___closed__1;
    return v___x_1282_;
}
pub unsafe fn l_instReprUnit___lam__0___boxed(
    mut v_x_1283_: *mut leanh::LeanObject,
    mut v_x_1284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1285_ = l_instReprUnit___lam__0(v_x_1283_, v_x_1284_);
    leanh::lean_dec(v_x_1284_);
    return v_res_1285_;
}
pub unsafe fn l_Option_repr___redArg(
    mut v_inst_1294_: *mut leanh::LeanObject,
    mut v_x_1295_: *mut leanh::LeanObject,
    mut v_x_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1295_) == 0 {
        let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1294_);
        v___x_1297_ = l_Option_repr___redArg___closed__1;
        return v___x_1297_;
    } else {
        let mut v_val_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1298_ = leanh::lean_ctor_get(v_x_1295_, 0);
        leanh::lean_inc(v_val_1298_);
        leanh::lean_dec_ref_known(v_x_1295_, 1);
        v___x_1299_ = l_Option_repr___redArg___closed__3;
        v___x_1300_ = leanh::lean_unsigned_to_nat(1024);
        v___x_1301_ = leanh::lean_apply_2(v_inst_1294_, v_val_1298_, v___x_1300_);
        v___x_1302_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1302_, 0, v___x_1299_);
        leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
        v___x_1303_ = l_Repr_addAppParen(v___x_1302_, v_x_1296_);
        return v___x_1303_;
    }
}
pub unsafe fn l_Option_repr___redArg___boxed(
    mut v_inst_1304_: *mut leanh::LeanObject,
    mut v_x_1305_: *mut leanh::LeanObject,
    mut v_x_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_Option_repr___redArg(v_inst_1304_, v_x_1305_, v_x_1306_);
    leanh::lean_dec(v_x_1306_);
    return v_res_1307_;
}
pub unsafe fn l_Option_repr(
    mut v_00_u03b1_1308_: *mut leanh::LeanObject,
    mut v_inst_1309_: *mut leanh::LeanObject,
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v_x_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1312_ = l_Option_repr___redArg(v_inst_1309_, v_x_1310_, v_x_1311_);
    return v___x_1312_;
}
pub unsafe fn l_Option_repr___boxed(
    mut v_00_u03b1_1313_: *mut leanh::LeanObject,
    mut v_inst_1314_: *mut leanh::LeanObject,
    mut v_x_1315_: *mut leanh::LeanObject,
    mut v_x_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1317_ = l_Option_repr(v_00_u03b1_1313_, v_inst_1314_, v_x_1315_, v_x_1316_);
    leanh::lean_dec(v_x_1316_);
    return v_res_1317_;
}
pub unsafe fn l_instReprOption___redArg(
    mut v_inst_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ =
        leanh::lean_alloc_closure(l_Option_repr___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1319_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1319_, 1, v_inst_1318_);
    return v___x_1319_;
}
pub unsafe fn l_instReprOption(
    mut v_00_u03b1_1320_: *mut leanh::LeanObject,
    mut v_inst_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ =
        leanh::lean_alloc_closure(l_Option_repr___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_1322_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1322_, 1, v_inst_1321_);
    return v___x_1322_;
}
pub unsafe fn l_Sum_repr___redArg(
    mut v_inst_1329_: *mut leanh::LeanObject,
    mut v_inst_1330_: *mut leanh::LeanObject,
    mut v_x_1331_: *mut leanh::LeanObject,
    mut v_x_1332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1331_) == 0 {
        let mut v_val_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1330_);
        v_val_1333_ = leanh::lean_ctor_get(v_x_1331_, 0);
        leanh::lean_inc(v_val_1333_);
        leanh::lean_dec_ref_known(v_x_1331_, 1);
        v___x_1334_ = l_Sum_repr___redArg___closed__1;
        v___x_1335_ = leanh::lean_unsigned_to_nat(1024);
        v___x_1336_ = leanh::lean_apply_2(v_inst_1329_, v_val_1333_, v___x_1335_);
        v___x_1337_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1337_, 0, v___x_1334_);
        leanh::lean_ctor_set(v___x_1337_, 1, v___x_1336_);
        v___x_1338_ = l_Repr_addAppParen(v___x_1337_, v_x_1332_);
        return v___x_1338_;
    } else {
        let mut v_val_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_1329_);
        v_val_1339_ = leanh::lean_ctor_get(v_x_1331_, 0);
        leanh::lean_inc(v_val_1339_);
        leanh::lean_dec_ref_known(v_x_1331_, 1);
        v___x_1340_ = l_Sum_repr___redArg___closed__3;
        v___x_1341_ = leanh::lean_unsigned_to_nat(1024);
        v___x_1342_ = leanh::lean_apply_2(v_inst_1330_, v_val_1339_, v___x_1341_);
        v___x_1343_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_1343_, 0, v___x_1340_);
        leanh::lean_ctor_set(v___x_1343_, 1, v___x_1342_);
        v___x_1344_ = l_Repr_addAppParen(v___x_1343_, v_x_1332_);
        return v___x_1344_;
    }
}
pub unsafe fn l_Sum_repr___redArg___boxed(
    mut v_inst_1345_: *mut leanh::LeanObject,
    mut v_inst_1346_: *mut leanh::LeanObject,
    mut v_x_1347_: *mut leanh::LeanObject,
    mut v_x_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Sum_repr___redArg(v_inst_1345_, v_inst_1346_, v_x_1347_, v_x_1348_);
    leanh::lean_dec(v_x_1348_);
    return v_res_1349_;
}
pub unsafe fn l_Sum_repr(
    mut v_00_u03b1_1350_: *mut leanh::LeanObject,
    mut v_00_u03b2_1351_: *mut leanh::LeanObject,
    mut v_inst_1352_: *mut leanh::LeanObject,
    mut v_inst_1353_: *mut leanh::LeanObject,
    mut v_x_1354_: *mut leanh::LeanObject,
    mut v_x_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Sum_repr___redArg(v_inst_1352_, v_inst_1353_, v_x_1354_, v_x_1355_);
    return v___x_1356_;
}
pub unsafe fn l_Sum_repr___boxed(
    mut v_00_u03b1_1357_: *mut leanh::LeanObject,
    mut v_00_u03b2_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
    mut v_inst_1360_: *mut leanh::LeanObject,
    mut v_x_1361_: *mut leanh::LeanObject,
    mut v_x_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1363_ = l_Sum_repr(
        v_00_u03b1_1357_,
        v_00_u03b2_1358_,
        v_inst_1359_,
        v_inst_1360_,
        v_x_1361_,
        v_x_1362_,
    );
    leanh::lean_dec(v_x_1362_);
    return v_res_1363_;
}
pub unsafe fn l_instReprSum___redArg(
    mut v_inst_1364_: *mut leanh::LeanObject,
    mut v_inst_1365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1366_ =
        leanh::lean_alloc_closure(l_Sum_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1366_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1366_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1366_, 2, v_inst_1364_);
    leanh::lean_closure_set(v___x_1366_, 3, v_inst_1365_);
    return v___x_1366_;
}
pub unsafe fn l_instReprSum(
    mut v_00_u03b1_1367_: *mut leanh::LeanObject,
    mut v_00_u03b2_1368_: *mut leanh::LeanObject,
    mut v_inst_1369_: *mut leanh::LeanObject,
    mut v_inst_1370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1371_ =
        leanh::lean_alloc_closure(l_Sum_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1371_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1371_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1371_, 2, v_inst_1369_);
    leanh::lean_closure_set(v___x_1371_, 3, v_inst_1370_);
    return v___x_1371_;
}
pub unsafe fn l_instReprTupleOfRepr___redArg___lam__0(
    mut v_inst_1372_: *mut leanh::LeanObject,
    mut v_a_1373_: *mut leanh::LeanObject,
    mut v_xs_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = leanh::lean_unsigned_to_nat(0);
    v___x_1376_ = leanh::lean_apply_2(v_inst_1372_, v_a_1373_, v___x_1375_);
    v___x_1377_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1377_, 0, v___x_1376_);
    leanh::lean_ctor_set(v___x_1377_, 1, v_xs_1374_);
    return v___x_1377_;
}
pub unsafe fn l_instReprTupleOfRepr___redArg(
    mut v_inst_1378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1379_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1379_, 0, v_inst_1378_);
    return v___f_1379_;
}
pub unsafe fn l_instReprTupleOfRepr(
    mut v_00_u03b1_1380_: *mut leanh::LeanObject,
    mut v_inst_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1382_ = leanh::lean_alloc_closure(
        l_instReprTupleOfRepr___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1382_, 0, v_inst_1381_);
    return v___f_1382_;
}
pub unsafe fn l_Prod_reprTuple___redArg(
    mut v_inst_1383_: *mut leanh::LeanObject,
    mut v_inst_1384_: *mut leanh::LeanObject,
    mut v_x_1385_: *mut leanh::LeanObject,
    mut v_x_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1391_: u8 = 0;
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1387_ = leanh::lean_ctor_get(v_x_1385_, 0);
                v_snd_1388_ = leanh::lean_ctor_get(v_x_1385_, 1);
                v_isSharedCheck_1398_ = (!leanh::lean_is_exclusive(v_x_1385_)) as u8;
                if v_isSharedCheck_1398_ == 0 {
                    v___x_1390_ = v_x_1385_;
                    v_isShared_1391_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1388_);
                    leanh::lean_inc(v_fst_1387_);
                    leanh::lean_dec(v_x_1385_);
                    v___x_1390_ = leanh::lean_box(0);
                    v_isShared_1391_ = v_isSharedCheck_1398_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1392_ = leanh::lean_unsigned_to_nat(0);
                v___x_1393_ = leanh::lean_apply_2(v_inst_1383_, v_fst_1387_, v___x_1392_);
                if v_isShared_1391_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1390_, 1);
                    leanh::lean_ctor_set(v___x_1390_, 1, v_x_1386_);
                    leanh::lean_ctor_set(v___x_1390_, 0, v___x_1393_);
                    v___x_1395_ = v___x_1390_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1393_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_x_1386_);
                    v___x_1395_ = v_reuseFailAlloc_1397_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1396_ = leanh::lean_apply_2(v_inst_1384_, v_snd_1388_, v___x_1395_);
                return v___x_1396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_reprTuple(
    mut v_00_u03b1_1399_: *mut leanh::LeanObject,
    mut v_00_u03b2_1400_: *mut leanh::LeanObject,
    mut v_inst_1401_: *mut leanh::LeanObject,
    mut v_inst_1402_: *mut leanh::LeanObject,
    mut v_x_1403_: *mut leanh::LeanObject,
    mut v_x_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1405_ = l_Prod_reprTuple___redArg(v_inst_1401_, v_inst_1402_, v_x_1403_, v_x_1404_);
    return v___x_1405_;
}
pub unsafe fn l_instReprTupleProdOfRepr___redArg(
    mut v_inst_1406_: *mut leanh::LeanObject,
    mut v_inst_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ =
        leanh::lean_alloc_closure(l_Prod_reprTuple as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1408_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1408_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1408_, 2, v_inst_1406_);
    leanh::lean_closure_set(v___x_1408_, 3, v_inst_1407_);
    return v___x_1408_;
}
pub unsafe fn l_instReprTupleProdOfRepr(
    mut v_00_u03b1_1409_: *mut leanh::LeanObject,
    mut v_00_u03b2_1410_: *mut leanh::LeanObject,
    mut v_inst_1411_: *mut leanh::LeanObject,
    mut v_inst_1412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1413_ =
        leanh::lean_alloc_closure(l_Prod_reprTuple as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1413_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1413_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1413_, 2, v_inst_1411_);
    leanh::lean_closure_set(v___x_1413_, 3, v_inst_1412_);
    return v___x_1413_;
}
pub unsafe fn _init_l_Prod_repr___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1421_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2),
        core::ptr::addr_of_mut!(l_Repr_addAppParen___closed__2_once),
        _init_l_Repr_addAppParen___closed__2,
    );
    v___x_1422_ = lean_nat_to_int(v___x_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Prod_repr___redArg(
    mut v_inst_1423_: *mut leanh::LeanObject,
    mut v_inst_1424_: *mut leanh::LeanObject,
    mut v_x_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___f_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: u8 = 0;
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1426_ = leanh::lean_ctor_get(v_x_1425_, 0);
                v_snd_1427_ = leanh::lean_ctor_get(v_x_1425_, 1);
                v_isSharedCheck_1450_ = (!leanh::lean_is_exclusive(v_x_1425_)) as u8;
                if v_isSharedCheck_1450_ == 0 {
                    v___x_1429_ = v_x_1425_;
                    v_isShared_1430_ = v_isSharedCheck_1450_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1427_);
                    leanh::lean_inc(v_fst_1426_);
                    leanh::lean_dec(v_x_1425_);
                    v___x_1429_ = leanh::lean_box(0);
                    v_isShared_1430_ = v_isSharedCheck_1450_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1431_ = l_Prod_repr___redArg___closed__0;
                v___x_1432_ = leanh::lean_unsigned_to_nat(0);
                v___x_1433_ = leanh::lean_apply_2(v_inst_1423_, v_fst_1426_, v___x_1432_);
                v___x_1434_ = leanh::lean_box(0);
                if v_isShared_1430_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1429_, 1);
                    leanh::lean_ctor_set(v___x_1429_, 1, v___x_1434_);
                    leanh::lean_ctor_set(v___x_1429_, 0, v___x_1433_);
                    v___x_1436_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1449_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1449_, 1, v___x_1434_);
                    v___x_1436_ = v_reuseFailAlloc_1449_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1437_ = leanh::lean_apply_2(v_inst_1424_, v_snd_1427_, v___x_1436_);
                v___x_1438_ = l_List_reverse___redArg(v___x_1437_);
                v___x_1439_ = l_Prod_repr___redArg___closed__3;
                v___x_1440_ = l_Std_Format_joinSep___redArg(v___f_1431_, v___x_1438_, v___x_1439_);
                v___x_1441_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Prod_repr___redArg___closed__4),
                    core::ptr::addr_of_mut!(l_Prod_repr___redArg___closed__4_once),
                    _init_l_Prod_repr___redArg___closed__4,
                );
                v___x_1442_ = l_Repr_addAppParen___closed__4;
                v___x_1443_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
                leanh::lean_ctor_set(v___x_1443_, 1, v___x_1440_);
                v___x_1444_ = l_Repr_addAppParen___closed__5;
                v___x_1445_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1445_, 0, v___x_1443_);
                leanh::lean_ctor_set(v___x_1445_, 1, v___x_1444_);
                v___x_1446_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1446_, 0, v___x_1441_);
                leanh::lean_ctor_set(v___x_1446_, 1, v___x_1445_);
                v___x_1447_ = 0;
                v___x_1448_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1448_, 0, v___x_1446_);
                leanh::lean_ctor_set_uint8(
                    v___x_1448_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1447_,
                );
                return v___x_1448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Prod_repr(
    mut v_00_u03b1_1451_: *mut leanh::LeanObject,
    mut v_00_u03b2_1452_: *mut leanh::LeanObject,
    mut v_inst_1453_: *mut leanh::LeanObject,
    mut v_inst_1454_: *mut leanh::LeanObject,
    mut v_x_1455_: *mut leanh::LeanObject,
    mut v_x_1456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = l_Prod_repr___redArg(v_inst_1453_, v_inst_1454_, v_x_1455_);
    return v___x_1457_;
}
pub unsafe fn l_Prod_repr___boxed(
    mut v_00_u03b1_1458_: *mut leanh::LeanObject,
    mut v_00_u03b2_1459_: *mut leanh::LeanObject,
    mut v_inst_1460_: *mut leanh::LeanObject,
    mut v_inst_1461_: *mut leanh::LeanObject,
    mut v_x_1462_: *mut leanh::LeanObject,
    mut v_x_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1464_ = l_Prod_repr(
        v_00_u03b1_1458_,
        v_00_u03b2_1459_,
        v_inst_1460_,
        v_inst_1461_,
        v_x_1462_,
        v_x_1463_,
    );
    leanh::lean_dec(v_x_1463_);
    return v_res_1464_;
}
pub unsafe fn l_instReprProdOfReprTuple___redArg(
    mut v_inst_1465_: *mut leanh::LeanObject,
    mut v_inst_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1467_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1467_, 2, v_inst_1465_);
    leanh::lean_closure_set(v___x_1467_, 3, v_inst_1466_);
    return v___x_1467_;
}
pub unsafe fn l_instReprProdOfReprTuple(
    mut v_00_u03b1_1468_: *mut leanh::LeanObject,
    mut v_00_u03b2_1469_: *mut leanh::LeanObject,
    mut v_inst_1470_: *mut leanh::LeanObject,
    mut v_inst_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ =
        leanh::lean_alloc_closure(l_Prod_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1472_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1472_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1472_, 2, v_inst_1470_);
    leanh::lean_closure_set(v___x_1472_, 3, v_inst_1471_);
    return v___x_1472_;
}
pub unsafe fn _init_l_Sigma_repr___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Sigma_repr___redArg___closed__0;
    v___x_1479_ = lean_string_length(v___x_1478_);
    return v___x_1479_;
}
pub unsafe fn _init_l_Sigma_repr___redArg___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__4_once),
        _init_l_Sigma_repr___redArg___closed__4,
    );
    v___x_1481_ = lean_nat_to_int(v___x_1480_);
    return v___x_1481_;
}
pub unsafe fn l_Sigma_repr___redArg(
    mut v_inst_1486_: *mut leanh::LeanObject,
    mut v_inst_1487_: *mut leanh::LeanObject,
    mut v_x_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1489_ = leanh::lean_ctor_get(v_x_1488_, 0);
                v_snd_1490_ = leanh::lean_ctor_get(v_x_1488_, 1);
                v_isSharedCheck_1510_ = (!leanh::lean_is_exclusive(v_x_1488_)) as u8;
                if v_isSharedCheck_1510_ == 0 {
                    v___x_1492_ = v_x_1488_;
                    v_isShared_1493_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1490_);
                    leanh::lean_inc(v_fst_1489_);
                    leanh::lean_dec(v_x_1488_);
                    v___x_1492_ = leanh::lean_box(0);
                    v_isShared_1493_ = v_isSharedCheck_1510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1494_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc(v_fst_1489_);
                v___x_1495_ = leanh::lean_apply_2(v_inst_1486_, v_fst_1489_, v___x_1494_);
                v___x_1496_ = l_Sigma_repr___redArg___closed__2;
                if v_isShared_1493_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1492_, 5);
                    leanh::lean_ctor_set(v___x_1492_, 1, v___x_1496_);
                    leanh::lean_ctor_set(v___x_1492_, 0, v___x_1495_);
                    v___x_1498_ = v___x_1492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1496_);
                    v___x_1498_ = v_reuseFailAlloc_1509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1499_ =
                    leanh::lean_apply_3(v_inst_1487_, v_fst_1489_, v_snd_1490_, v___x_1494_);
                v___x_1500_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1500_, 0, v___x_1498_);
                leanh::lean_ctor_set(v___x_1500_, 1, v___x_1499_);
                v___x_1501_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__5),
                    core::ptr::addr_of_mut!(l_Sigma_repr___redArg___closed__5_once),
                    _init_l_Sigma_repr___redArg___closed__5,
                );
                v___x_1502_ = l_Sigma_repr___redArg___closed__6;
                v___x_1503_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1503_, 0, v___x_1502_);
                leanh::lean_ctor_set(v___x_1503_, 1, v___x_1500_);
                v___x_1504_ = l_Sigma_repr___redArg___closed__7;
                v___x_1505_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1505_, 0, v___x_1503_);
                leanh::lean_ctor_set(v___x_1505_, 1, v___x_1504_);
                v___x_1506_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1506_, 0, v___x_1501_);
                leanh::lean_ctor_set(v___x_1506_, 1, v___x_1505_);
                v___x_1507_ = 0;
                v___x_1508_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1508_, 0, v___x_1506_);
                leanh::lean_ctor_set_uint8(
                    v___x_1508_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1507_,
                );
                return v___x_1508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Sigma_repr(
    mut v_00_u03b1_1511_: *mut leanh::LeanObject,
    mut v_00_u03b2_1512_: *mut leanh::LeanObject,
    mut v_inst_1513_: *mut leanh::LeanObject,
    mut v_inst_1514_: *mut leanh::LeanObject,
    mut v_x_1515_: *mut leanh::LeanObject,
    mut v_x_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_Sigma_repr___redArg(v_inst_1513_, v_inst_1514_, v_x_1515_);
    return v___x_1517_;
}
pub unsafe fn l_Sigma_repr___boxed(
    mut v_00_u03b1_1518_: *mut leanh::LeanObject,
    mut v_00_u03b2_1519_: *mut leanh::LeanObject,
    mut v_inst_1520_: *mut leanh::LeanObject,
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_x_1522_: *mut leanh::LeanObject,
    mut v_x_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_Sigma_repr(
        v_00_u03b1_1518_,
        v_00_u03b2_1519_,
        v_inst_1520_,
        v_inst_1521_,
        v_x_1522_,
        v_x_1523_,
    );
    leanh::lean_dec(v_x_1523_);
    return v_res_1524_;
}
pub unsafe fn l_instReprSigma___redArg(
    mut v_inst_1525_: *mut leanh::LeanObject,
    mut v_inst_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1527_ =
        leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1527_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1527_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1527_, 2, v_inst_1525_);
    leanh::lean_closure_set(v___x_1527_, 3, v_inst_1526_);
    return v___x_1527_;
}
pub unsafe fn l_instReprSigma(
    mut v_00_u03b1_1528_: *mut leanh::LeanObject,
    mut v_00_u03b2_1529_: *mut leanh::LeanObject,
    mut v_inst_1530_: *mut leanh::LeanObject,
    mut v_inst_1531_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1532_ =
        leanh::lean_alloc_closure(l_Sigma_repr___boxed as *mut core::ffi::c_void, 6, 4);
    leanh::lean_closure_set(v___x_1532_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1532_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1532_, 2, v_inst_1530_);
    leanh::lean_closure_set(v___x_1532_, 3, v_inst_1531_);
    return v___x_1532_;
}
pub unsafe fn l_instReprSubtype___redArg___lam__0(
    mut v_inst_1533_: *mut leanh::LeanObject,
    mut v_s_1534_: *mut leanh::LeanObject,
    mut v_prec_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = leanh::lean_apply_2(v_inst_1533_, v_s_1534_, v_prec_1535_);
    return v___x_1536_;
}
pub unsafe fn l_instReprSubtype___redArg(
    mut v_inst_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1538_ = leanh::lean_alloc_closure(
        l_instReprSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1538_, 0, v_inst_1537_);
    return v___f_1538_;
}
pub unsafe fn l_instReprSubtype(
    mut v_00_u03b1_1539_: *mut leanh::LeanObject,
    mut v_p_1540_: *mut leanh::LeanObject,
    mut v_inst_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1542_ = leanh::lean_alloc_closure(
        l_instReprSubtype___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1542_, 0, v_inst_1541_);
    return v___f_1542_;
}
pub unsafe fn l_Nat_digitChar(mut v_n_1543_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: u8 = 0;
    v___x_1544_ = leanh::lean_unsigned_to_nat(0);
    v___x_1545_ = lean_nat_dec_eq(v_n_1543_, v___x_1544_);
    if v___x_1545_ == 0 {
        let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: u8 = 0;
        v___x_1546_ = leanh::lean_unsigned_to_nat(1);
        v___x_1547_ = lean_nat_dec_eq(v_n_1543_, v___x_1546_);
        if v___x_1547_ == 0 {
            let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1549_: u8 = 0;
            v___x_1548_ = leanh::lean_unsigned_to_nat(2);
            v___x_1549_ = lean_nat_dec_eq(v_n_1543_, v___x_1548_);
            if v___x_1549_ == 0 {
                let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1551_: u8 = 0;
                v___x_1550_ = leanh::lean_unsigned_to_nat(3);
                v___x_1551_ = lean_nat_dec_eq(v_n_1543_, v___x_1550_);
                if v___x_1551_ == 0 {
                    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1553_: u8 = 0;
                    v___x_1552_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1553_ = lean_nat_dec_eq(v_n_1543_, v___x_1552_);
                    if v___x_1553_ == 0 {
                        let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1555_: u8 = 0;
                        v___x_1554_ = leanh::lean_unsigned_to_nat(5);
                        v___x_1555_ = lean_nat_dec_eq(v_n_1543_, v___x_1554_);
                        if v___x_1555_ == 0 {
                            let mut v___x_1556_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1557_: u8 = 0;
                            v___x_1556_ = leanh::lean_unsigned_to_nat(6);
                            v___x_1557_ = lean_nat_dec_eq(v_n_1543_, v___x_1556_);
                            if v___x_1557_ == 0 {
                                let mut v___x_1558_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1559_: u8 = 0;
                                v___x_1558_ = leanh::lean_unsigned_to_nat(7);
                                v___x_1559_ = lean_nat_dec_eq(v_n_1543_, v___x_1558_);
                                if v___x_1559_ == 0 {
                                    let mut v___x_1560_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1561_: u8 = 0;
                                    v___x_1560_ = leanh::lean_unsigned_to_nat(8);
                                    v___x_1561_ = lean_nat_dec_eq(v_n_1543_, v___x_1560_);
                                    if v___x_1561_ == 0 {
                                        let mut v___x_1562_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1563_: u8 = 0;
                                        v___x_1562_ = leanh::lean_unsigned_to_nat(9);
                                        v___x_1563_ = lean_nat_dec_eq(v_n_1543_, v___x_1562_);
                                        if v___x_1563_ == 0 {
                                            let mut v___x_1564_: *mut leanh::LeanObject =
                                                core::ptr::null_mut();
                                            let mut v___x_1565_: u8 = 0;
                                            v___x_1564_ = leanh::lean_unsigned_to_nat(10);
                                            v___x_1565_ = lean_nat_dec_eq(v_n_1543_, v___x_1564_);
                                            if v___x_1565_ == 0 {
                                                let mut v___x_1566_: *mut leanh::LeanObject =
                                                    core::ptr::null_mut();
                                                let mut v___x_1567_: u8 = 0;
                                                v___x_1566_ =
                                                    leanh::lean_unsigned_to_nat(11);
                                                v___x_1567_ =
                                                    lean_nat_dec_eq(v_n_1543_, v___x_1566_);
                                                if v___x_1567_ == 0 {
                                                    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                    let mut v___x_1569_: u8 = 0;
                                                    v___x_1568_ =
                                                        leanh::lean_unsigned_to_nat(12);
                                                    v___x_1569_ =
                                                        lean_nat_dec_eq(v_n_1543_, v___x_1568_);
                                                    if v___x_1569_ == 0 {
                                                        let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                        let mut v___x_1571_: u8 = 0;
                                                        v___x_1570_ =
                                                            leanh::lean_unsigned_to_nat(13);
                                                        v___x_1571_ =
                                                            lean_nat_dec_eq(v_n_1543_, v___x_1570_);
                                                        if v___x_1571_ == 0 {
                                                            let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                            let mut v___x_1573_: u8 = 0;
                                                            v___x_1572_ =
                                                                leanh::lean_unsigned_to_nat(
                                                                    14,
                                                                );
                                                            v___x_1573_ = lean_nat_dec_eq(
                                                                v_n_1543_,
                                                                v___x_1572_,
                                                            );
                                                            if v___x_1573_ == 0 {
                                                                let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
                                                                let mut v___x_1575_: u8 = 0;
                                                                v___x_1574_ = leanh::lean_unsigned_to_nat(15);
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
    mut v_n_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1594_: u32 = 0;
    let mut v_r_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1594_ = l_Nat_digitChar(v_n_1593_);
    leanh::lean_dec(v_n_1593_);
    v_r_1595_ = leanh::lean_box_uint32(v_res_1594_);
    return v_r_1595_;
}
pub unsafe fn l_Nat_toDigitsCore(
    mut v_base_1596_: *mut leanh::LeanObject,
    mut v_x_1597_: *mut leanh::LeanObject,
    mut v_x_1598_: *mut leanh::LeanObject,
    mut v_x_1599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1601_: u8 = 0;
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1603_: u32 = 0;
    let mut v_n_x27_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v_one_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1600_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1601_ = lean_nat_dec_eq(v_x_1597_, v_zero_1600_);
                if v_isZero_1601_ == 1 {
                    leanh::lean_dec(v_x_1598_);
                    leanh::lean_dec(v_x_1597_);
                    return v_x_1599_;
                } else {
                    v___x_1602_ = lean_nat_mod(v_x_1598_, v_base_1596_);
                    v_d_1603_ = l_Nat_digitChar(v___x_1602_);
                    leanh::lean_dec(v___x_1602_);
                    v_n_x27_1604_ = lean_nat_div(v_x_1598_, v_base_1596_);
                    leanh::lean_dec(v_x_1598_);
                    v___x_1605_ = lean_nat_dec_eq(v_n_x27_1604_, v_zero_1600_);
                    if v___x_1605_ == 0 {
                        v_one_1606_ = leanh::lean_unsigned_to_nat(1);
                        v_n_1607_ = lean_nat_sub(v_x_1597_, v_one_1606_);
                        leanh::lean_dec(v_x_1597_);
                        v___x_1608_ = leanh::lean_box_uint32(v_d_1603_);
                        v___x_1609_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1609_, 0, v___x_1608_);
                        leanh::lean_ctor_set(v___x_1609_, 1, v_x_1599_);
                        v_x_1597_ = v_n_1607_;
                        v_x_1598_ = v_n_x27_1604_;
                        v_x_1599_ = v___x_1609_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_x27_1604_);
                        leanh::lean_dec(v_x_1597_);
                        v___x_1611_ = leanh::lean_box_uint32(v_d_1603_);
                        v___x_1612_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1612_, 0, v___x_1611_);
                        leanh::lean_ctor_set(v___x_1612_, 1, v_x_1599_);
                        return v___x_1612_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toDigitsCore___boxed(
    mut v_base_1613_: *mut leanh::LeanObject,
    mut v_x_1614_: *mut leanh::LeanObject,
    mut v_x_1615_: *mut leanh::LeanObject,
    mut v_x_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1617_ = l_Nat_toDigitsCore(v_base_1613_, v_x_1614_, v_x_1615_, v_x_1616_);
    leanh::lean_dec(v_base_1613_);
    return v_res_1617_;
}
pub unsafe fn l_Nat_toDigits(
    mut v_base_1618_: *mut leanh::LeanObject,
    mut v_n_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = leanh::lean_unsigned_to_nat(1);
    v___x_1621_ = lean_nat_add(v_n_1619_, v___x_1620_);
    v___x_1622_ = leanh::lean_box(0);
    v___x_1623_ = l_Nat_toDigitsCore(v_base_1618_, v___x_1621_, v_n_1619_, v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn l_Nat_toDigits___boxed(
    mut v_base_1624_: *mut leanh::LeanObject,
    mut v_n_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Nat_toDigits(v_base_1624_, v_n_1625_);
    leanh::lean_dec(v_base_1624_);
    return v_res_1626_;
}
pub unsafe fn l_USize_repr___boxed(
    mut v_n_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1629_: usize = 0;
    let mut v_res_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1629_ = leanh::lean_unbox_usize(v_n_1628_);
    leanh::lean_dec(v_n_1628_);
    v_res_1630_ = lean_string_of_usize(v_n_boxed_1629_);
    return v_res_1630_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Init_Data_Repr_0__Nat_reprArray_spec__0(
    mut v_a_1631_: *mut leanh::LeanObject,
    mut v_a_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1639_: usize = 0;
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1645_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1631_) == 0 {
                    v___x_1633_ = l_List_reverse___redArg(v_a_1632_);
                    return v___x_1633_;
                } else {
                    v_head_1634_ = leanh::lean_ctor_get(v_a_1631_, 0);
                    v_tail_1635_ = leanh::lean_ctor_get(v_a_1631_, 1);
                    v_isSharedCheck_1645_ = (!leanh::lean_is_exclusive(v_a_1631_)) as u8;
                    if v_isSharedCheck_1645_ == 0 {
                        v___x_1637_ = v_a_1631_;
                        v_isShared_1638_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1635_);
                        leanh::lean_inc(v_head_1634_);
                        leanh::lean_dec(v_a_1631_);
                        v___x_1637_ = leanh::lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1645_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1639_ = lean_usize_of_nat(v_head_1634_);
                leanh::lean_dec(v_head_1634_);
                v___x_1640_ = lean_string_of_usize(v___x_1639_);
                if v_isShared_1638_ == 0 {
                    leanh::lean_ctor_set(v___x_1637_, 1, v_a_1632_);
                    leanh::lean_ctor_set(v___x_1637_, 0, v___x_1640_);
                    v___x_1642_ = v___x_1637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1644_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_a_1632_);
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
-> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1646_ = leanh::lean_unsigned_to_nat(128);
    v___x_1647_ = l_List_range(v___x_1646_);
    return v___x_1647_;
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = leanh::lean_box(0);
    v___x_1649_ = leanh::lean_obj_once(
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
-> *mut leanh::LeanObject {
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__1),
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__1_once),
        _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__1,
    );
    v___x_1652_ = lean_array_mk(v___x_1651_);
    return v___x_1652_;
}
pub unsafe fn _init_l___private_Init_Data_Repr_0__Nat_reprArray() -> *mut leanh::LeanObject {
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1653_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__2),
        core::ptr::addr_of_mut!(l___private_Init_Data_Repr_0__Nat_reprArray___closed__2_once),
        _init_l___private_Init_Data_Repr_0__Nat_reprArray___closed__2,
    );
    return v___x_1653_;
}
pub unsafe fn _init_l_Nat_reprFast___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = l___private_Init_Data_Repr_0__Nat_reprArray;
    v___x_1655_ = lean_array_get_size(v___x_1654_);
    return v___x_1655_;
}
pub unsafe fn _init_l_Nat_reprFast___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_System_Platform_numBits;
    v___x_1657_ = leanh::lean_unsigned_to_nat(2);
    v___x_1658_ = lean_nat_pow(v___x_1657_, v___x_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Nat_reprFast(
    mut v_n_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: u8 = 0;
    v___x_1660_ = l___private_Init_Data_Repr_0__Nat_reprArray;
    v___x_1661_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Nat_reprFast___closed__0),
        core::ptr::addr_of_mut!(l_Nat_reprFast___closed__0_once),
        _init_l_Nat_reprFast___closed__0,
    );
    v___x_1662_ = lean_nat_dec_lt(v_n_1659_, v___x_1661_);
    if v___x_1662_ == 0 {
        let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1664_: u8 = 0;
        v___x_1663_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Nat_reprFast___closed__1),
            core::ptr::addr_of_mut!(l_Nat_reprFast___closed__1_once),
            _init_l_Nat_reprFast___closed__1,
        );
        v___x_1664_ = lean_nat_dec_lt(v_n_1659_, v___x_1663_);
        if v___x_1664_ == 0 {
            let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1665_ = leanh::lean_unsigned_to_nat(10);
            v___x_1666_ = l_Nat_toDigits(v___x_1665_, v_n_1659_);
            v___x_1667_ = lean_string_mk(v___x_1666_);
            return v___x_1667_;
        } else {
            let mut v___x_1668_: usize = 0;
            let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1668_ = lean_usize_of_nat(v_n_1659_);
            leanh::lean_dec(v_n_1659_);
            v___x_1669_ = lean_string_of_usize(v___x_1668_);
            return v___x_1669_;
        }
    } else {
        let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1670_ = lean_array_fget_borrowed(v___x_1660_, v_n_1659_);
        leanh::lean_dec(v_n_1659_);
        leanh::lean_inc(v___x_1670_);
        return v___x_1670_;
    }
}
pub unsafe fn l_Nat_superDigitChar(mut v_n_1671_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: u8 = 0;
    v___x_1672_ = leanh::lean_unsigned_to_nat(0);
    v___x_1673_ = lean_nat_dec_eq(v_n_1671_, v___x_1672_);
    if v___x_1673_ == 0 {
        let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1675_: u8 = 0;
        v___x_1674_ = leanh::lean_unsigned_to_nat(1);
        v___x_1675_ = lean_nat_dec_eq(v_n_1671_, v___x_1674_);
        if v___x_1675_ == 0 {
            let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1677_: u8 = 0;
            v___x_1676_ = leanh::lean_unsigned_to_nat(2);
            v___x_1677_ = lean_nat_dec_eq(v_n_1671_, v___x_1676_);
            if v___x_1677_ == 0 {
                let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1679_: u8 = 0;
                v___x_1678_ = leanh::lean_unsigned_to_nat(3);
                v___x_1679_ = lean_nat_dec_eq(v_n_1671_, v___x_1678_);
                if v___x_1679_ == 0 {
                    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1681_: u8 = 0;
                    v___x_1680_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1681_ = lean_nat_dec_eq(v_n_1671_, v___x_1680_);
                    if v___x_1681_ == 0 {
                        let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1683_: u8 = 0;
                        v___x_1682_ = leanh::lean_unsigned_to_nat(5);
                        v___x_1683_ = lean_nat_dec_eq(v_n_1671_, v___x_1682_);
                        if v___x_1683_ == 0 {
                            let mut v___x_1684_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1685_: u8 = 0;
                            v___x_1684_ = leanh::lean_unsigned_to_nat(6);
                            v___x_1685_ = lean_nat_dec_eq(v_n_1671_, v___x_1684_);
                            if v___x_1685_ == 0 {
                                let mut v___x_1686_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1687_: u8 = 0;
                                v___x_1686_ = leanh::lean_unsigned_to_nat(7);
                                v___x_1687_ = lean_nat_dec_eq(v_n_1671_, v___x_1686_);
                                if v___x_1687_ == 0 {
                                    let mut v___x_1688_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1689_: u8 = 0;
                                    v___x_1688_ = leanh::lean_unsigned_to_nat(8);
                                    v___x_1689_ = lean_nat_dec_eq(v_n_1671_, v___x_1688_);
                                    if v___x_1689_ == 0 {
                                        let mut v___x_1690_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1691_: u8 = 0;
                                        v___x_1690_ = leanh::lean_unsigned_to_nat(9);
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
    mut v_n_1703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1704_: u32 = 0;
    let mut v_r_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1704_ = l_Nat_superDigitChar(v_n_1703_);
    leanh::lean_dec(v_n_1703_);
    v_r_1705_ = leanh::lean_box_uint32(v_res_1704_);
    return v_r_1705_;
}
pub unsafe fn l_Nat_toSuperDigitsAux(
    mut v_x_1706_: *mut leanh::LeanObject,
    mut v_x_1707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1710_: u32 = 0;
    let mut v_n_x27_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1708_ = leanh::lean_unsigned_to_nat(10);
                v___x_1709_ = lean_nat_mod(v_x_1706_, v___x_1708_);
                v_d_1710_ = l_Nat_superDigitChar(v___x_1709_);
                leanh::lean_dec(v___x_1709_);
                v_n_x27_1711_ = lean_nat_div(v_x_1706_, v___x_1708_);
                leanh::lean_dec(v_x_1706_);
                v___x_1712_ = leanh::lean_unsigned_to_nat(0);
                v___x_1713_ = lean_nat_dec_eq(v_n_x27_1711_, v___x_1712_);
                if v___x_1713_ == 0 {
                    v___x_1714_ = leanh::lean_box_uint32(v_d_1710_);
                    v___x_1715_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1715_, 0, v___x_1714_);
                    leanh::lean_ctor_set(v___x_1715_, 1, v_x_1707_);
                    v_x_1706_ = v_n_x27_1711_;
                    v_x_1707_ = v___x_1715_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_n_x27_1711_);
                    v___x_1717_ = leanh::lean_box_uint32(v_d_1710_);
                    v___x_1718_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
                    leanh::lean_ctor_set(v___x_1718_, 1, v_x_1707_);
                    return v___x_1718_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toSuperDigits(
    mut v_n_1719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1720_ = leanh::lean_box(0);
    v___x_1721_ = l_Nat_toSuperDigitsAux(v_n_1719_, v___x_1720_);
    return v___x_1721_;
}
pub unsafe fn l_Nat_toSuperscriptString(
    mut v_n_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = l_Nat_toSuperDigits(v_n_1722_);
    v___x_1724_ = lean_string_mk(v___x_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Nat_subDigitChar(mut v_n_1725_: *mut leanh::LeanObject) -> u32 {
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    v___x_1726_ = leanh::lean_unsigned_to_nat(0);
    v___x_1727_ = lean_nat_dec_eq(v_n_1725_, v___x_1726_);
    if v___x_1727_ == 0 {
        let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1729_: u8 = 0;
        v___x_1728_ = leanh::lean_unsigned_to_nat(1);
        v___x_1729_ = lean_nat_dec_eq(v_n_1725_, v___x_1728_);
        if v___x_1729_ == 0 {
            let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1731_: u8 = 0;
            v___x_1730_ = leanh::lean_unsigned_to_nat(2);
            v___x_1731_ = lean_nat_dec_eq(v_n_1725_, v___x_1730_);
            if v___x_1731_ == 0 {
                let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1733_: u8 = 0;
                v___x_1732_ = leanh::lean_unsigned_to_nat(3);
                v___x_1733_ = lean_nat_dec_eq(v_n_1725_, v___x_1732_);
                if v___x_1733_ == 0 {
                    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1735_: u8 = 0;
                    v___x_1734_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1735_ = lean_nat_dec_eq(v_n_1725_, v___x_1734_);
                    if v___x_1735_ == 0 {
                        let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1737_: u8 = 0;
                        v___x_1736_ = leanh::lean_unsigned_to_nat(5);
                        v___x_1737_ = lean_nat_dec_eq(v_n_1725_, v___x_1736_);
                        if v___x_1737_ == 0 {
                            let mut v___x_1738_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_1739_: u8 = 0;
                            v___x_1738_ = leanh::lean_unsigned_to_nat(6);
                            v___x_1739_ = lean_nat_dec_eq(v_n_1725_, v___x_1738_);
                            if v___x_1739_ == 0 {
                                let mut v___x_1740_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1741_: u8 = 0;
                                v___x_1740_ = leanh::lean_unsigned_to_nat(7);
                                v___x_1741_ = lean_nat_dec_eq(v_n_1725_, v___x_1740_);
                                if v___x_1741_ == 0 {
                                    let mut v___x_1742_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_1743_: u8 = 0;
                                    v___x_1742_ = leanh::lean_unsigned_to_nat(8);
                                    v___x_1743_ = lean_nat_dec_eq(v_n_1725_, v___x_1742_);
                                    if v___x_1743_ == 0 {
                                        let mut v___x_1744_: *mut leanh::LeanObject =
                                            core::ptr::null_mut();
                                        let mut v___x_1745_: u8 = 0;
                                        v___x_1744_ = leanh::lean_unsigned_to_nat(9);
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
    mut v_n_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1758_: u32 = 0;
    let mut v_r_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = l_Nat_subDigitChar(v_n_1757_);
    leanh::lean_dec(v_n_1757_);
    v_r_1759_ = leanh::lean_box_uint32(v_res_1758_);
    return v_r_1759_;
}
pub unsafe fn l_Nat_toSubDigitsAux(
    mut v_x_1760_: *mut leanh::LeanObject,
    mut v_x_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1764_: u32 = 0;
    let mut v_n_x27_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1762_ = leanh::lean_unsigned_to_nat(10);
                v___x_1763_ = lean_nat_mod(v_x_1760_, v___x_1762_);
                v_d_1764_ = l_Nat_subDigitChar(v___x_1763_);
                leanh::lean_dec(v___x_1763_);
                v_n_x27_1765_ = lean_nat_div(v_x_1760_, v___x_1762_);
                leanh::lean_dec(v_x_1760_);
                v___x_1766_ = leanh::lean_unsigned_to_nat(0);
                v___x_1767_ = lean_nat_dec_eq(v_n_x27_1765_, v___x_1766_);
                if v___x_1767_ == 0 {
                    v___x_1768_ = leanh::lean_box_uint32(v_d_1764_);
                    v___x_1769_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1769_, 0, v___x_1768_);
                    leanh::lean_ctor_set(v___x_1769_, 1, v_x_1761_);
                    v_x_1760_ = v_n_x27_1765_;
                    v_x_1761_ = v___x_1769_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_n_x27_1765_);
                    v___x_1771_ = leanh::lean_box_uint32(v_d_1764_);
                    v___x_1772_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1772_, 0, v___x_1771_);
                    leanh::lean_ctor_set(v___x_1772_, 1, v_x_1761_);
                    return v___x_1772_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_toSubDigits(
    mut v_n_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = leanh::lean_box(0);
    v___x_1775_ = l_Nat_toSubDigitsAux(v_n_1773_, v___x_1774_);
    return v___x_1775_;
}
pub unsafe fn l_Nat_toSubscriptString(
    mut v_n_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1777_ = l_Nat_toSubDigits(v_n_1776_);
    v___x_1778_ = lean_string_mk(v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_instReprNat___lam__0(
    mut v_n_1779_: *mut leanh::LeanObject,
    mut v_x_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1781_ = l_Nat_reprFast(v_n_1779_);
    v___x_1782_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1781_);
    return v___x_1782_;
}
pub unsafe fn l_instReprNat___lam__0___boxed(
    mut v_n_1783_: *mut leanh::LeanObject,
    mut v_x_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_instReprNat___lam__0(v_n_1783_, v_x_1784_);
    leanh::lean_dec(v_x_1784_);
    return v_res_1785_;
}
pub unsafe fn l_hexDigitRepr(
    mut v_n_1789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1790_: u32 = 0;
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1790_ = l_Nat_digitChar(v_n_1789_);
    v___x_1791_ = l_hexDigitRepr___closed__0;
    v___x_1792_ = lean_string_push(v___x_1791_, v___x_1790_);
    return v___x_1792_;
}
pub unsafe fn l_hexDigitRepr___boxed(
    mut v_n_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1794_ = l_hexDigitRepr(v_n_1793_);
    leanh::lean_dec(v_n_1793_);
    return v_res_1794_;
}
pub unsafe fn l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(
    mut v_c_1795_: u32,
) -> *mut leanh::LeanObject {
    let mut v_n_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d2_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d1_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_1796_ = lean_uint32_to_nat(v_c_1795_);
    v___x_1797_ = leanh::lean_unsigned_to_nat(16);
    v___x_1798_ = leanh::lean_unsigned_to_nat(4);
    v_d2_1799_ = lean_nat_shiftr(v_n_1796_, v___x_1798_);
    v_d1_1800_ = lean_nat_mod(v_n_1796_, v___x_1797_);
    leanh::lean_dec(v_n_1796_);
    v___x_1801_ = l_hexDigitRepr(v_d2_1799_);
    leanh::lean_dec(v_d2_1799_);
    v___x_1802_ = l_hexDigitRepr(v_d1_1800_);
    leanh::lean_dec(v_d1_1800_);
    v___x_1803_ = lean_string_append(v___x_1801_, v___x_1802_);
    leanh::lean_dec_ref(v___x_1802_);
    return v___x_1803_;
}
pub unsafe fn l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex___boxed(
    mut v_c_1804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1805_: u32 = 0;
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1805_ = leanh::lean_unbox_uint32(v_c_1804_);
    leanh::lean_dec(v_c_1804_);
    v_res_1806_ = l___private_Init_Data_Repr_0__Char_quoteCore_smallCharToHex(v_c_boxed_1805_);
    return v_res_1806_;
}
pub unsafe fn l_Char_quoteCore(
    mut v_c_1813_: u32,
    mut v_inString_1814_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: u32 = 0;
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                leanh::lean_dec_ref(v___x_1817_);
                return v___x_1818_;
            }
            2 => {
                v___x_1820_ = lean_uint32_to_nat(v_c_1813_);
                v___x_1821_ = leanh::lean_unsigned_to_nat(31);
                v___x_1822_ = lean_nat_dec_le(v___x_1820_, v___x_1821_);
                leanh::lean_dec(v___x_1820_);
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
    mut v_c_1842_: *mut leanh::LeanObject,
    mut v_inString_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1844_: u32 = 0;
    let mut v_inString_boxed_1845_: u8 = 0;
    let mut v_res_1846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1844_ = leanh::lean_unbox_uint32(v_c_1842_);
    leanh::lean_dec(v_c_1842_);
    v_inString_boxed_1845_ = (leanh::lean_unbox(v_inString_1843_) as u8);
    v_res_1846_ = l_Char_quoteCore(v_c_boxed_1844_, v_inString_boxed_1845_);
    return v_res_1846_;
}
pub unsafe fn l_Char_quote(mut v_c_1848_: u32) -> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Char_quote___closed__0;
    v___x_1850_ = 0;
    v___x_1851_ = l_Char_quoteCore(v_c_1848_, v___x_1850_);
    v___x_1852_ = lean_string_append(v___x_1849_, v___x_1851_);
    leanh::lean_dec_ref(v___x_1851_);
    v___x_1853_ = lean_string_append(v___x_1852_, v___x_1849_);
    return v___x_1853_;
}
pub unsafe fn l_Char_quote___boxed(
    mut v_c_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1855_: u32 = 0;
    let mut v_res_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1855_ = leanh::lean_unbox_uint32(v_c_1854_);
    leanh::lean_dec(v_c_1854_);
    v_res_1856_ = l_Char_quote(v_c_boxed_1855_);
    return v_res_1856_;
}
pub unsafe fn l_instReprChar___lam__0(
    mut v_c_1857_: u32,
    mut v_x_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Char_quote(v_c_1857_);
    v___x_1860_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    return v___x_1860_;
}
pub unsafe fn l_instReprChar___lam__0___boxed(
    mut v_c_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1863_: u32 = 0;
    let mut v_res_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1863_ = leanh::lean_unbox_uint32(v_c_1861_);
    leanh::lean_dec(v_c_1861_);
    v_res_1864_ = l_instReprChar___lam__0(v_c_boxed_1863_, v_x_1862_);
    leanh::lean_dec(v_x_1862_);
    return v_res_1864_;
}
pub unsafe fn l_Char_repr(mut v_c_1867_: u32) -> *mut leanh::LeanObject {
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = l_Char_quote(v_c_1867_);
    return v___x_1868_;
}
pub unsafe fn l_Char_repr___boxed(
    mut v_c_1869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1870_: u32 = 0;
    let mut v_res_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1870_ = leanh::lean_unbox_uint32(v_c_1869_);
    leanh::lean_dec(v_c_1869_);
    v_res_1871_ = l_Char_repr(v_c_boxed_1870_);
    return v_res_1871_;
}
pub unsafe fn l_String_quote___lam__0(
    mut v___x_1872_: u8,
    mut v_s_1873_: *mut leanh::LeanObject,
    mut v_c_1874_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1875_ = l_Char_quoteCore(v_c_1874_, v___x_1872_);
    v___x_1876_ = lean_string_append(v_s_1873_, v___x_1875_);
    leanh::lean_dec_ref(v___x_1875_);
    return v___x_1876_;
}
pub unsafe fn l_String_quote___lam__0___boxed(
    mut v___x_1877_: *mut leanh::LeanObject,
    mut v_s_1878_: *mut leanh::LeanObject,
    mut v_c_1879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_43__boxed_1880_: u8 = 0;
    let mut v_c_boxed_1881_: u32 = 0;
    let mut v_res_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_43__boxed_1880_ = (leanh::lean_unbox(v___x_1877_) as u8);
    v_c_boxed_1881_ = leanh::lean_unbox_uint32(v_c_1879_);
    leanh::lean_dec(v_c_1879_);
    v_res_1882_ = l_String_quote___lam__0(v___x_43__boxed_1880_, v_s_1878_, v_c_boxed_1881_);
    return v_res_1882_;
}
pub unsafe fn l_String_quote(
    mut v_s_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1889_: u8 = 0;
    leanh::lean_inc_ref(v_s_1888_);
    v___x_1889_ = lean_string_isempty(v_s_1888_);
    if v___x_1889_ == 0 {
        let mut v___f_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_1890_ = l_String_quote___closed__0;
        v___x_1891_ = l_String_quote___closed__1;
        v___x_1892_ = lean_string_foldl(v___f_1890_, v___x_1891_, v_s_1888_);
        v___x_1893_ = lean_string_append(v___x_1892_, v___x_1891_);
        return v___x_1893_;
    } else {
        let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_1888_);
        v___x_1894_ = l_String_quote___closed__2;
        return v___x_1894_;
    }
}
pub unsafe fn l_instReprString___lam__0(
    mut v_s_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1897_ = l_String_quote(v_s_1895_);
    v___x_1898_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1898_, 0, v___x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_instReprString___lam__0___boxed(
    mut v_s_1899_: *mut leanh::LeanObject,
    mut v_x_1900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1901_ = l_instReprString___lam__0(v_s_1899_, v_x_1900_);
    leanh::lean_dec(v_x_1900_);
    return v_res_1901_;
}
pub unsafe fn l_instReprRaw___lam__0(
    mut v_p_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1912_ = l_instReprRaw___lam__0___closed__1;
    v___x_1913_ = l_Nat_reprFast(v_p_1910_);
    v___x_1914_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1914_, 0, v___x_1913_);
    v___x_1915_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1915_, 0, v___x_1912_);
    leanh::lean_ctor_set(v___x_1915_, 1, v___x_1914_);
    v___x_1916_ = l_instReprRaw___lam__0___closed__3;
    v___x_1917_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1917_, 0, v___x_1915_);
    leanh::lean_ctor_set(v___x_1917_, 1, v___x_1916_);
    return v___x_1917_;
}
pub unsafe fn l_instReprRaw___lam__0___boxed(
    mut v_p_1918_: *mut leanh::LeanObject,
    mut v_x_1919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1920_ = l_instReprRaw___lam__0(v_p_1918_, v_x_1919_);
    leanh::lean_dec(v_x_1919_);
    return v_res_1920_;
}
pub unsafe fn l_instReprRaw__1___lam__0(
    mut v_s_1924_: *mut leanh::LeanObject,
    mut v_x_1925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1926_ = lean_substring_tostring(v_s_1924_);
    v___x_1927_ = l_String_quote(v___x_1926_);
    v___x_1928_ = l_instReprRaw__1___lam__0___closed__0;
    v___x_1929_ = lean_string_append(v___x_1927_, v___x_1928_);
    v___x_1930_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1930_, 0, v___x_1929_);
    return v___x_1930_;
}
pub unsafe fn l_instReprRaw__1___lam__0___boxed(
    mut v_s_1931_: *mut leanh::LeanObject,
    mut v_x_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_instReprRaw__1___lam__0(v_s_1931_, v_x_1932_);
    leanh::lean_dec(v_x_1932_);
    return v_res_1933_;
}
pub unsafe fn l_instReprFin___lam__0(
    mut v_f_1936_: *mut leanh::LeanObject,
    mut v_x_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Nat_reprFast(v_f_1936_);
    v___x_1939_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1939_, 0, v___x_1938_);
    return v___x_1939_;
}
pub unsafe fn l_instReprFin___lam__0___boxed(
    mut v_f_1940_: *mut leanh::LeanObject,
    mut v_x_1941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1942_ = l_instReprFin___lam__0(v_f_1940_, v_x_1941_);
    leanh::lean_dec(v_x_1941_);
    return v_res_1942_;
}
pub unsafe fn l_instReprFin(
    mut v_n_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1945_ = l_instReprFin___closed__0;
    return v___f_1945_;
}
pub unsafe fn l_instReprFin___boxed(
    mut v_n_1946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1947_ = l_instReprFin(v_n_1946_);
    leanh::lean_dec(v_n_1946_);
    return v_res_1947_;
}
pub unsafe fn l_instReprUInt8___lam__0(
    mut v_n_1948_: u8,
    mut v_x_1949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = lean_uint8_to_nat(v_n_1948_);
    v___x_1951_ = l_Nat_reprFast(v___x_1950_);
    v___x_1952_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1952_, 0, v___x_1951_);
    return v___x_1952_;
}
pub unsafe fn l_instReprUInt8___lam__0___boxed(
    mut v_n_1953_: *mut leanh::LeanObject,
    mut v_x_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1955_: u8 = 0;
    let mut v_res_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1955_ = (leanh::lean_unbox(v_n_1953_) as u8);
    v_res_1956_ = l_instReprUInt8___lam__0(v_n_boxed_1955_, v_x_1954_);
    leanh::lean_dec(v_x_1954_);
    return v_res_1956_;
}
pub unsafe fn l_instReprUInt16___lam__0(
    mut v_n_1959_: u16,
    mut v_x_1960_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = lean_uint16_to_nat(v_n_1959_);
    v___x_1962_ = l_Nat_reprFast(v___x_1961_);
    v___x_1963_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
    return v___x_1963_;
}
pub unsafe fn l_instReprUInt16___lam__0___boxed(
    mut v_n_1964_: *mut leanh::LeanObject,
    mut v_x_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1966_: u16 = 0;
    let mut v_res_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1966_ = (leanh::lean_unbox(v_n_1964_) as u16);
    v_res_1967_ = l_instReprUInt16___lam__0(v_n_boxed_1966_, v_x_1965_);
    leanh::lean_dec(v_x_1965_);
    return v_res_1967_;
}
pub unsafe fn l_instReprUInt32___lam__0(
    mut v_n_1970_: u32,
    mut v_x_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1972_ = lean_uint32_to_nat(v_n_1970_);
    v___x_1973_ = l_Nat_reprFast(v___x_1972_);
    v___x_1974_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1974_, 0, v___x_1973_);
    return v___x_1974_;
}
pub unsafe fn l_instReprUInt32___lam__0___boxed(
    mut v_n_1975_: *mut leanh::LeanObject,
    mut v_x_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1977_: u32 = 0;
    let mut v_res_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1977_ = leanh::lean_unbox_uint32(v_n_1975_);
    leanh::lean_dec(v_n_1975_);
    v_res_1978_ = l_instReprUInt32___lam__0(v_n_boxed_1977_, v_x_1976_);
    leanh::lean_dec(v_x_1976_);
    return v_res_1978_;
}
pub unsafe fn l_instReprUInt64___lam__0(
    mut v_n_1981_: u64,
    mut v_x_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1983_ = lean_uint64_to_nat(v_n_1981_);
    v___x_1984_ = l_Nat_reprFast(v___x_1983_);
    v___x_1985_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1985_, 0, v___x_1984_);
    return v___x_1985_;
}
pub unsafe fn l_instReprUInt64___lam__0___boxed(
    mut v_n_1986_: *mut leanh::LeanObject,
    mut v_x_1987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1988_: u64 = 0;
    let mut v_res_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1988_ = leanh::lean_unbox_uint64(v_n_1986_);
    leanh::lean_dec_ref(v_n_1986_);
    v_res_1989_ = l_instReprUInt64___lam__0(v_n_boxed_1988_, v_x_1987_);
    leanh::lean_dec(v_x_1987_);
    return v_res_1989_;
}
pub unsafe fn l_instReprUSize___lam__0(
    mut v_n_1992_: usize,
    mut v_x_1993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1994_ = lean_usize_to_nat(v_n_1992_);
    v___x_1995_ = l_Nat_reprFast(v___x_1994_);
    v___x_1996_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1996_, 0, v___x_1995_);
    return v___x_1996_;
}
pub unsafe fn l_instReprUSize___lam__0___boxed(
    mut v_n_1997_: *mut leanh::LeanObject,
    mut v_x_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_boxed_1999_: usize = 0;
    let mut v_res_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_1999_ = leanh::lean_unbox_usize(v_n_1997_);
    leanh::lean_dec(v_n_1997_);
    v_res_2000_ = l_instReprUSize___lam__0(v_n_boxed_1999_, v_x_1998_);
    leanh::lean_dec(v_x_1998_);
    return v_res_2000_;
}
pub unsafe fn _init_l_List_repr___redArg___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2008_ = l_List_repr___redArg___closed__2;
    v___x_2009_ = lean_string_length(v___x_2008_);
    return v___x_2009_;
}
pub unsafe fn _init_l_List_repr___redArg___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2010_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_List_repr___redArg___closed__4),
        core::ptr::addr_of_mut!(l_List_repr___redArg___closed__4_once),
        _init_l_List_repr___redArg___closed__4,
    );
    v___x_2011_ = lean_nat_to_int(v___x_2010_);
    return v___x_2011_;
}
pub unsafe fn l_List_repr___redArg(
    mut v_inst_2016_: *mut leanh::LeanObject,
    mut v_a_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2017_) == 0 {
        let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2016_);
        v___x_2018_ = l_List_repr___redArg___closed__1;
        return v___x_2018_;
    } else {
        let mut v_x_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2028_: u8 = 0;
        let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_2019_ = leanh::lean_alloc_closure(l_repr as *mut core::ffi::c_void, 3, 2);
        leanh::lean_closure_set(v_x_2019_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v_x_2019_, 1, v_inst_2016_);
        v___x_2020_ = l_Prod_repr___redArg___closed__3;
        v___x_2021_ = l_Std_Format_joinSep___redArg(v_x_2019_, v_a_2017_, v___x_2020_);
        v___x_2022_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5),
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5_once),
            _init_l_List_repr___redArg___closed__5,
        );
        v___x_2023_ = l_List_repr___redArg___closed__6;
        v___x_2024_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2024_, 0, v___x_2023_);
        leanh::lean_ctor_set(v___x_2024_, 1, v___x_2021_);
        v___x_2025_ = l_List_repr___redArg___closed__7;
        v___x_2026_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2026_, 0, v___x_2024_);
        leanh::lean_ctor_set(v___x_2026_, 1, v___x_2025_);
        v___x_2027_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2027_, 0, v___x_2022_);
        leanh::lean_ctor_set(v___x_2027_, 1, v___x_2026_);
        v___x_2028_ = 0;
        v___x_2029_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
        leanh::lean_ctor_set(v___x_2029_, 0, v___x_2027_);
        leanh::lean_ctor_set_uint8(
            v___x_2029_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
            v___x_2028_,
        );
        return v___x_2029_;
    }
}
pub unsafe fn l_List_repr(
    mut v_00_u03b1_2030_: *mut leanh::LeanObject,
    mut v_inst_2031_: *mut leanh::LeanObject,
    mut v_a_2032_: *mut leanh::LeanObject,
    mut v_n_2033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = l_List_repr___redArg(v_inst_2031_, v_a_2032_);
    return v___x_2034_;
}
pub unsafe fn l_List_repr___boxed(
    mut v_00_u03b1_2035_: *mut leanh::LeanObject,
    mut v_inst_2036_: *mut leanh::LeanObject,
    mut v_a_2037_: *mut leanh::LeanObject,
    mut v_n_2038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_List_repr(v_00_u03b1_2035_, v_inst_2036_, v_a_2037_, v_n_2038_);
    leanh::lean_dec(v_n_2038_);
    return v_res_2039_;
}
pub unsafe fn l_instReprList___redArg(
    mut v_inst_2040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2041_ =
        leanh::lean_alloc_closure(l_List_repr___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_2041_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2041_, 1, v_inst_2040_);
    return v___x_2041_;
}
pub unsafe fn l_instReprList(
    mut v_00_u03b1_2042_: *mut leanh::LeanObject,
    mut v_inst_2043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ =
        leanh::lean_alloc_closure(l_List_repr___boxed as *mut core::ffi::c_void, 4, 2);
    leanh::lean_closure_set(v___x_2044_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2044_, 1, v_inst_2043_);
    return v___x_2044_;
}
pub unsafe fn l_List_repr_x27___redArg(
    mut v_inst_2045_: *mut leanh::LeanObject,
    mut v_a_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_a_2046_) == 0 {
        let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2045_);
        v___x_2047_ = l_List_repr___redArg___closed__1;
        return v___x_2047_;
    } else {
        let mut v_x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_2048_ = leanh::lean_alloc_closure(l_repr as *mut core::ffi::c_void, 3, 2);
        leanh::lean_closure_set(v_x_2048_, 0, leanh::lean_box(0));
        leanh::lean_closure_set(v_x_2048_, 1, v_inst_2045_);
        v___x_2049_ = l_Prod_repr___redArg___closed__3;
        v___x_2050_ = l_Std_Format_joinSep___redArg(v_x_2048_, v_a_2046_, v___x_2049_);
        v___x_2051_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5),
            core::ptr::addr_of_mut!(l_List_repr___redArg___closed__5_once),
            _init_l_List_repr___redArg___closed__5,
        );
        v___x_2052_ = l_List_repr___redArg___closed__6;
        v___x_2053_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2053_, 0, v___x_2052_);
        leanh::lean_ctor_set(v___x_2053_, 1, v___x_2050_);
        v___x_2054_ = l_List_repr___redArg___closed__7;
        v___x_2055_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2055_, 0, v___x_2053_);
        leanh::lean_ctor_set(v___x_2055_, 1, v___x_2054_);
        v___x_2056_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2056_, 0, v___x_2051_);
        leanh::lean_ctor_set(v___x_2056_, 1, v___x_2055_);
        v___x_2057_ = l_Std_Format_fill(v___x_2056_);
        return v___x_2057_;
    }
}
pub unsafe fn l_List_repr_x27(
    mut v_00_u03b1_2058_: *mut leanh::LeanObject,
    mut v_inst_2059_: *mut leanh::LeanObject,
    mut v_inst_2060_: *mut leanh::LeanObject,
    mut v_a_2061_: *mut leanh::LeanObject,
    mut v_n_2062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = l_List_repr_x27___redArg(v_inst_2059_, v_a_2061_);
    return v___x_2063_;
}
pub unsafe fn l_List_repr_x27___boxed(
    mut v_00_u03b1_2064_: *mut leanh::LeanObject,
    mut v_inst_2065_: *mut leanh::LeanObject,
    mut v_inst_2066_: *mut leanh::LeanObject,
    mut v_a_2067_: *mut leanh::LeanObject,
    mut v_n_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2069_ = l_List_repr_x27(
        v_00_u03b1_2064_,
        v_inst_2065_,
        v_inst_2066_,
        v_a_2067_,
        v_n_2068_,
    );
    leanh::lean_dec(v_n_2068_);
    return v_res_2069_;
}
pub unsafe fn l_instReprListOfReprAtom___redArg(
    mut v_inst_2070_: *mut leanh::LeanObject,
    mut v_inst_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ =
        leanh::lean_alloc_closure(l_List_repr_x27___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2072_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2072_, 1, v_inst_2070_);
    leanh::lean_closure_set(v___x_2072_, 2, v_inst_2071_);
    return v___x_2072_;
}
pub unsafe fn l_instReprListOfReprAtom(
    mut v_00_u03b1_2073_: *mut leanh::LeanObject,
    mut v_inst_2074_: *mut leanh::LeanObject,
    mut v_inst_2075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2076_ =
        leanh::lean_alloc_closure(l_List_repr_x27___boxed as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_2076_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2076_, 1, v_inst_2074_);
    leanh::lean_closure_set(v___x_2076_, 2, v_inst_2075_);
    return v___x_2076_;
}
pub unsafe fn _init_l_instReprAtomBool() -> *mut leanh::LeanObject {
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2077_ = leanh::lean_box(0);
    return v___x_2077_;
}
pub unsafe fn _init_l_instReprAtomNat() -> *mut leanh::LeanObject {
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2078_ = leanh::lean_box(0);
    return v___x_2078_;
}
pub unsafe fn _init_l_instReprAtomInt() -> *mut leanh::LeanObject {
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2079_ = leanh::lean_box(0);
    return v___x_2079_;
}
pub unsafe fn _init_l_instReprAtomChar() -> *mut leanh::LeanObject {
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2080_ = leanh::lean_box(0);
    return v___x_2080_;
}
pub unsafe fn _init_l_instReprAtomString() -> *mut leanh::LeanObject {
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2081_ = leanh::lean_box(0);
    return v___x_2081_;
}
pub unsafe fn _init_l_instReprAtomUInt8() -> *mut leanh::LeanObject {
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2082_ = leanh::lean_box(0);
    return v___x_2082_;
}
pub unsafe fn _init_l_instReprAtomUInt16() -> *mut leanh::LeanObject {
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2083_ = leanh::lean_box(0);
    return v___x_2083_;
}
pub unsafe fn _init_l_instReprAtomUInt32() -> *mut leanh::LeanObject {
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2084_ = leanh::lean_box(0);
    return v___x_2084_;
}
pub unsafe fn _init_l_instReprAtomUInt64() -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = leanh::lean_box(0);
    return v___x_2085_;
}
pub unsafe fn _init_l_instReprAtomUSize() -> *mut leanh::LeanObject {
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2086_ = leanh::lean_box(0);
    return v___x_2086_;
}
pub unsafe fn _init_l_instReprSourceInfo_repr___closed__5() -> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = leanh::lean_unsigned_to_nat(2);
    v___x_2097_ = lean_nat_to_int(v___x_2096_);
    return v___x_2097_;
}
pub unsafe fn _init_l_instReprSourceInfo_repr___closed__6() -> *mut leanh::LeanObject {
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2098_ = leanh::lean_unsigned_to_nat(1);
    v___x_2099_ = lean_nat_to_int(v___x_2098_);
    return v___x_2099_;
}
pub unsafe fn l_instReprSourceInfo_repr(
    mut v_x_2106_: *mut leanh::LeanObject,
    mut v_prec_2107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: u8 = 0;
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: u8 = 0;
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canonical_2159_: u8 = 0;
    let mut v___y_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: u8 = 0;
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: u8 = 0;
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_2106_) {
                0 => {
                    v_leading_2115_ = leanh::lean_ctor_get(v_x_2106_, 0);
                    leanh::lean_inc_ref(v_leading_2115_);
                    v_pos_2116_ = leanh::lean_ctor_get(v_x_2106_, 1);
                    leanh::lean_inc(v_pos_2116_);
                    v_trailing_2117_ = leanh::lean_ctor_get(v_x_2106_, 2);
                    leanh::lean_inc_ref(v_trailing_2117_);
                    v_endPos_2118_ = leanh::lean_ctor_get(v_x_2106_, 3);
                    leanh::lean_inc(v_endPos_2118_);
                    leanh::lean_dec_ref_known(v_x_2106_, 4);
                    v___x_2153_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2154_ = lean_nat_dec_le(v___x_2153_, v_prec_2107_);
                    if v___x_2154_ == 0 {
                        v___x_2155_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2120_ = v___x_2155_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2156_ = leanh::lean_obj_once(
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
                    v_pos_2157_ = leanh::lean_ctor_get(v_x_2106_, 0);
                    leanh::lean_inc(v_pos_2157_);
                    v_endPos_2158_ = leanh::lean_ctor_get(v_x_2106_, 1);
                    leanh::lean_inc(v_endPos_2158_);
                    v_canonical_2159_ = leanh::lean_ctor_get_uint8(
                        v_x_2106_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    leanh::lean_dec_ref_known(v_x_2106_, 2);
                    v___x_2184_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2185_ = lean_nat_dec_le(v___x_2184_, v_prec_2107_);
                    if v___x_2185_ == 0 {
                        v___x_2186_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2161_ = v___x_2186_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2187_ = leanh::lean_obj_once(
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
                    v___x_2188_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_2189_ = lean_nat_dec_le(v___x_2188_, v_prec_2107_);
                    if v___x_2189_ == 0 {
                        v___x_2190_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5),
                            core::ptr::addr_of_mut!(l_instReprSourceInfo_repr___closed__5_once),
                            _init_l_instReprSourceInfo_repr___closed__5,
                        );
                        v___y_2109_ = v___x_2190_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2191_ = leanh::lean_obj_once(
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
                leanh::lean_inc(v___y_2109_);
                v___x_2111_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2111_, 0, v___y_2109_);
                leanh::lean_ctor_set(v___x_2111_, 1, v___x_2110_);
                v___x_2112_ = 0;
                v___x_2113_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2113_, 0, v___x_2111_);
                leanh::lean_ctor_set_uint8(
                    v___x_2113_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2112_,
                );
                v___x_2114_ = l_Repr_addAppParen(v___x_2113_, v_prec_2107_);
                return v___x_2114_;
            }
            2 => {
                v___x_2121_ = leanh::lean_box(1);
                v___x_2122_ = l_instReprSourceInfo_repr___closed__4;
                v___x_2123_ = lean_substring_tostring(v_leading_2115_);
                v___x_2124_ = l_String_quote(v___x_2123_);
                v___x_2125_ = l_instReprRaw__1___lam__0___closed__0;
                v___x_2126_ = lean_string_append(v___x_2124_, v___x_2125_);
                v___x_2127_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2127_, 0, v___x_2126_);
                v___x_2128_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2128_, 0, v___x_2122_);
                leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                v___x_2129_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2129_, 0, v___x_2128_);
                leanh::lean_ctor_set(v___x_2129_, 1, v___x_2121_);
                v___x_2130_ = l_instReprRaw___lam__0___closed__1;
                v___x_2131_ = l_Nat_reprFast(v_pos_2116_);
                v___x_2132_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2132_, 0, v___x_2131_);
                v___x_2133_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2133_, 0, v___x_2130_);
                leanh::lean_ctor_set(v___x_2133_, 1, v___x_2132_);
                v___x_2134_ = l_instReprRaw___lam__0___closed__3;
                v___x_2135_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2135_, 0, v___x_2133_);
                leanh::lean_ctor_set(v___x_2135_, 1, v___x_2134_);
                v___x_2136_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2136_, 0, v___x_2129_);
                leanh::lean_ctor_set(v___x_2136_, 1, v___x_2135_);
                v___x_2137_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2137_, 0, v___x_2136_);
                leanh::lean_ctor_set(v___x_2137_, 1, v___x_2121_);
                v___x_2138_ = lean_substring_tostring(v_trailing_2117_);
                v___x_2139_ = l_String_quote(v___x_2138_);
                v___x_2140_ = lean_string_append(v___x_2139_, v___x_2125_);
                v___x_2141_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2141_, 0, v___x_2140_);
                v___x_2142_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2142_, 0, v___x_2137_);
                leanh::lean_ctor_set(v___x_2142_, 1, v___x_2141_);
                v___x_2143_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2143_, 0, v___x_2142_);
                leanh::lean_ctor_set(v___x_2143_, 1, v___x_2121_);
                v___x_2144_ = l_Nat_reprFast(v_endPos_2118_);
                v___x_2145_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2145_, 0, v___x_2144_);
                v___x_2146_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2146_, 0, v___x_2130_);
                leanh::lean_ctor_set(v___x_2146_, 1, v___x_2145_);
                v___x_2147_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                leanh::lean_ctor_set(v___x_2147_, 1, v___x_2134_);
                v___x_2148_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2148_, 0, v___x_2143_);
                leanh::lean_ctor_set(v___x_2148_, 1, v___x_2147_);
                leanh::lean_inc(v___y_2120_);
                v___x_2149_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2149_, 0, v___y_2120_);
                leanh::lean_ctor_set(v___x_2149_, 1, v___x_2148_);
                v___x_2150_ = 0;
                v___x_2151_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2151_, 0, v___x_2149_);
                leanh::lean_ctor_set_uint8(
                    v___x_2151_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_2150_,
                );
                v___x_2152_ = l_Repr_addAppParen(v___x_2151_, v_prec_2107_);
                return v___x_2152_;
            }
            3 => {
                v___x_2162_ = leanh::lean_box(1);
                v___x_2163_ = l_instReprSourceInfo_repr___closed__9;
                v___x_2164_ = l_instReprRaw___lam__0___closed__1;
                v___x_2165_ = l_Nat_reprFast(v_pos_2157_);
                v___x_2166_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2166_, 0, v___x_2165_);
                v___x_2167_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2167_, 0, v___x_2164_);
                leanh::lean_ctor_set(v___x_2167_, 1, v___x_2166_);
                v___x_2168_ = l_instReprRaw___lam__0___closed__3;
                v___x_2169_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2169_, 0, v___x_2167_);
                leanh::lean_ctor_set(v___x_2169_, 1, v___x_2168_);
                v___x_2170_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2170_, 0, v___x_2163_);
                leanh::lean_ctor_set(v___x_2170_, 1, v___x_2169_);
                v___x_2171_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                leanh::lean_ctor_set(v___x_2171_, 1, v___x_2162_);
                v___x_2172_ = l_Nat_reprFast(v_endPos_2158_);
                v___x_2173_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
                v___x_2174_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2174_, 0, v___x_2164_);
                leanh::lean_ctor_set(v___x_2174_, 1, v___x_2173_);
                v___x_2175_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2175_, 0, v___x_2174_);
                leanh::lean_ctor_set(v___x_2175_, 1, v___x_2168_);
                v___x_2176_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2176_, 0, v___x_2171_);
                leanh::lean_ctor_set(v___x_2176_, 1, v___x_2175_);
                v___x_2177_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2177_, 0, v___x_2176_);
                leanh::lean_ctor_set(v___x_2177_, 1, v___x_2162_);
                v___x_2178_ = l_Bool_repr___redArg(v_canonical_2159_);
                v___x_2179_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2179_, 0, v___x_2177_);
                leanh::lean_ctor_set(v___x_2179_, 1, v___x_2178_);
                leanh::lean_inc(v___y_2161_);
                v___x_2180_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2180_, 0, v___y_2161_);
                leanh::lean_ctor_set(v___x_2180_, 1, v___x_2179_);
                v___x_2181_ = 0;
                v___x_2182_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_2182_, 0, v___x_2180_);
                leanh::lean_ctor_set_uint8(
                    v___x_2182_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_2192_: *mut leanh::LeanObject,
    mut v_prec_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_instReprSourceInfo_repr(v_x_2192_, v_prec_2193_);
    leanh::lean_dec(v_prec_2193_);
    return v_res_2194_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Repr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Id(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Init_Data_Repr_0__Nat_reprArray =
        _init_l___private_Init_Data_Repr_0__Nat_reprArray();
    leanh::lean_mark_persistent(l___private_Init_Data_Repr_0__Nat_reprArray);
    l_instReprAtomBool = _init_l_instReprAtomBool();
    leanh::lean_mark_persistent(l_instReprAtomBool);
    l_instReprAtomNat = _init_l_instReprAtomNat();
    leanh::lean_mark_persistent(l_instReprAtomNat);
    l_instReprAtomInt = _init_l_instReprAtomInt();
    leanh::lean_mark_persistent(l_instReprAtomInt);
    l_instReprAtomChar = _init_l_instReprAtomChar();
    leanh::lean_mark_persistent(l_instReprAtomChar);
    l_instReprAtomString = _init_l_instReprAtomString();
    leanh::lean_mark_persistent(l_instReprAtomString);
    l_instReprAtomUInt8 = _init_l_instReprAtomUInt8();
    leanh::lean_mark_persistent(l_instReprAtomUInt8);
    l_instReprAtomUInt16 = _init_l_instReprAtomUInt16();
    leanh::lean_mark_persistent(l_instReprAtomUInt16);
    l_instReprAtomUInt32 = _init_l_instReprAtomUInt32();
    leanh::lean_mark_persistent(l_instReprAtomUInt32);
    l_instReprAtomUInt64 = _init_l_instReprAtomUInt64();
    leanh::lean_mark_persistent(l_instReprAtomUInt64);
    l_instReprAtomUSize = _init_l_instReprAtomUSize();
    leanh::lean_mark_persistent(l_instReprAtomUSize);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Repr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Repr(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Format_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Id(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Repr(builtin);
}